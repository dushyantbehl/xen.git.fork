/******************************************************************************
 *
 * xc_mem_event.c
 *
 * Interface to low-level memory event functionality.
 *
 * Copyright (c) 2009 Citrix Systems, Inc. (Patrick Colp)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

#include "xc_private.h"
#include <xen/mem_event.h>

int xc_mem_event_control(xc_interface *xch, domid_t domain_id, unsigned int op,
                         unsigned int mode, uint32_t *port)
{
    DECLARE_DOMCTL;
    int rc;

    domctl.cmd = XEN_DOMCTL_mem_event_op;
    domctl.domain = domain_id;
    domctl.u.mem_event_op.op = op;
    domctl.u.mem_event_op.mode = mode;
    
    rc = do_domctl(xch, &domctl);
    if ( !rc && port )
        *port = domctl.u.mem_event_op.port;
    return rc;
}

int xc_mem_event_memop(xc_interface *xch, domid_t domain_id, 
                        unsigned int op, unsigned int mode,
                        uint64_t gfn, void *buffer)
{
    xen_mem_event_op_t meo;

    memset(&meo, 0, sizeof(meo));

    meo.op      = op;
    meo.domain  = domain_id;
    meo.gfn     = gfn;
    meo.buffer  = (unsigned long) buffer;

    return do_memory_op(xch, mode, &meo, sizeof(meo));
}

/*
 * Enables mem_event and initializes shared ring to communicate with hypervisor
 * returns 0 if success and if failure returns -errno with
 * errno properly set to indicate possible error.
 * param can be HVM_PARAM_PAGING/ACCESS/SHARING_RING_PFN
 */
int xc_mem_event_enable(xc_interface *xch, domid_t domain_id, int param,
                        uint32_t *port, void *ring_page,
                        mem_event_back_ring_t *back_ring)
{
    uint64_t pfn;
    xen_pfn_t ring_pfn, mmap_pfn;
    unsigned int op, mode;
    int rc1, rc2, saved_errno, err;

    ring_page = NULL;

    if ( !port )
    {
        errno = EINVAL;
        return -errno;
    }

    /* Pause the domain for ring page setup */
    rc1 = xc_domain_pause(xch, domain_id);
    if ( rc1 != 0 )
    {
        PERROR("Unable to pause domain\n");
        return -errno;
    }

    /* Get the pfn of the ring page */
    rc1 = xc_hvm_param_get(xch, domain_id, param, &pfn);
    if ( rc1 != 0 )
    {
        PERROR("Failed to get pfn of ring page\n");
        goto out;
    }

    ring_pfn = pfn;
    mmap_pfn = pfn;
    ring_page = xc_map_foreign_bulk(xch, domain_id,
                                    PROT_READ | PROT_WRITE, &mmap_pfn, &err, 1);
    if ( (err != 0) || (ring_page == NULL) )
    {
        /* Map failed, populate ring page */
        rc1 = xc_domain_populate_physmap_exact(xch, domain_id, 1, 0, 0,
                                              &ring_pfn);
        if ( rc1 != 0 )
        {
            PERROR("Failed to populate ring pfn\n");
            goto out;
        }

        mmap_pfn = ring_pfn;
        ring_page = xc_map_foreign_bulk(xch, domain_id, PROT_READ | PROT_WRITE,
                                        &mmap_pfn, &err, 1);
        if ( (err != 0) || (ring_page == NULL) )
        {
            PERROR("Could not map the ring page\n");
            rc1 = -1;
            goto out;
        }
    }

    /* Clear the ring page */
    memset(ring_page, 0, PAGE_SIZE);

    /* Initialise ring */
    SHARED_RING_INIT((mem_event_sring_t *)ring_page);
    BACK_RING_INIT(back_ring, (mem_event_sring_t *)ring_page, PAGE_SIZE);

    switch ( param )
    {
    case HVM_PARAM_PAGING_RING_PFN:
        op = XEN_DOMCTL_MEM_EVENT_OP_PAGING_ENABLE;
        mode = XEN_DOMCTL_MEM_EVENT_OP_PAGING;
        break;

    case HVM_PARAM_ACCESS_RING_PFN:
        op = XEN_DOMCTL_MEM_EVENT_OP_ACCESS_ENABLE;
        mode = XEN_DOMCTL_MEM_EVENT_OP_ACCESS;
        break;

    case HVM_PARAM_SHARING_RING_PFN:
        op = XEN_DOMCTL_MEM_EVENT_OP_SHARING_ENABLE;
        mode = XEN_DOMCTL_MEM_EVENT_OP_SHARING;
        break;

    /*
     * This is for the outside chance that the HVM_PARAM is valid but is invalid
     * as far as mem_event goes.
     */
    default:
        errno = EINVAL;
        rc1 = -1;
        goto out;
    }

    rc1 = xc_mem_event_control(xch, domain_id, op, mode, port);
    if ( rc1 != 0 )
    {
        PERROR("Failed to enable mem_event\n");
        goto out;
    }

    /* Remove the ring_pfn from the guest's physmap */
    rc1 = xc_domain_decrease_reservation_exact(xch, domain_id, 1, 0, &ring_pfn);
    if ( rc1 != 0 )
    {
        PERROR("Failed to remove ring page from guest physmap");
        goto out;
    }

    rc1 = 0;

 out:
    saved_errno = errno;

    rc2 = xc_domain_unpause(xch, domain_id);
    if ( rc1 != 0 || rc2 != 0 )
    {
        if ( rc2 != 0 )
        {
            if ( rc1 == 0 )
                saved_errno = errno;
            PERROR("Unable to unpause domain");
        }

        if ( ring_page )
            munmap(ring_page, XC_PAGE_SIZE);
        ring_page = NULL;

        errno = saved_errno;
        rc1 = -errno;
    }

    return rc1;
}

/*
 * Teardown mem_event
 * returns 0 on success, if failure returns -errno with errno properly set.
 * param can be HVM_PARAM_PAGING/ACCESS/SHARING_RING_PFN
 */
int xc_mem_event_teardown(xc_interface *xch, domid_t domain_id,
                          int param, void *ring_page)
{
    int rc;
    unsigned int op, mode;

    switch ( param )
    {
        case HVM_PARAM_PAGING_RING_PFN:
            op = XEN_DOMCTL_MEM_EVENT_OP_PAGING_DISABLE;
            mode = XEN_DOMCTL_MEM_EVENT_OP_PAGING;
            break;

        case HVM_PARAM_ACCESS_RING_PFN:
            op = XEN_DOMCTL_MEM_EVENT_OP_ACCESS_DISABLE;
            mode = XEN_DOMCTL_MEM_EVENT_OP_ACCESS;
            break;

        case HVM_PARAM_SHARING_RING_PFN:
            op = XEN_DOMCTL_MEM_EVENT_OP_SHARING_DISABLE;
            mode = XEN_DOMCTL_MEM_EVENT_OP_SHARING;
            break;

        /*
         * This is for the outside chance that the HVM_PARAM is valid but is invalid
         * as far as mem_event goes.
         */
        default:
            errno = EINVAL;
            rc = -1;
            goto out;
    }

    /* Remove the ring page. */
    rc = munmap(ring_page, PAGE_SIZE);
    if ( rc < 0 )
        PERROR("Error while disabling paging in xen");

    ring_page = NULL;

    rc = xc_mem_event_control(xch, domain_id, op, mode, NULL);
    if ( rc != 0 )
    {
        PERROR("Failed to disable mem_event\n");
        goto out;
    }

  out:
    if (rc != 0)
        rc = -errno;

    return rc;
}
