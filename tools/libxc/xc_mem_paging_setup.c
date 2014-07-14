/*
 * tools/libxc/xc_mem_paging_setup.c
 *
 * Routines to initialize and teardown memory paging.
 * Create shared ring and event channels to communicate
 * with the hypervisor.
 *
 * Copyright (c) 2014 Dushyant Behl <myselfdushyantbehl@gmail.com>
 * Copyright (c) 2009 by Citrix Systems, Inc. (Patrick Colp)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301 USA
 */

#include "xg_private.h"
#include <xen/event_channel.h>
#include <xen/mem_event.h>

/*
 * Mem paging ring and event channel setup routine.
 * Setup a shared ring and an event channel to communicate between
 * hypervisor and the tool performing mem paging operations.
 * The function will return zero on successful completion and will
 * return -1 on failure at any intermediate step setting up errno
 * properly.
 */
int xc_mem_paging_ring_setup(xc_interface *xch,
                             xc_evtchn *xce_handle,
                             domid_t domain_id,
                             void *ring_page,
                             int *port,
                             uint32_t *evtchn_port,
                             mem_event_back_ring_t *back_ring)
{
    int rc, err;
    uint64_t pfn;
    xen_pfn_t ring_pfn, mmap_pfn;

    /* Map the ring page */
    xc_hvm_param_get(xch, domain_id, HVM_PARAM_PAGING_RING_PFN, &pfn);

    ring_pfn = pfn;
    mmap_pfn = ring_pfn;
    ring_page = xc_map_foreign_bulk(xch, domain_id,
                                    PROT_READ | PROT_WRITE, &mmap_pfn, &err, 1);
    if ( (err != 0) || (ring_page == NULL) )
    {
        /* Map failed, populate ring page */
        rc = xc_domain_populate_physmap_exact(xch, domain_id,
                                              1, 0, 0, &ring_pfn);
        if ( rc != 0 )
        {
            PERROR("Failed to populate ring gfn\n");
            return -1;
        }

        mmap_pfn = ring_pfn;
        ring_page = xc_map_foreign_bulk(xch, domain_id, PROT_READ | PROT_WRITE,
                                        &mmap_pfn, &err, 1);

        if ( (err != 0) || (ring_page == NULL) )
        {
            PERROR("Could not map the ring page\n");
            return -1;
        }
    }

    /* Initialise Xen */
    rc = xc_mem_paging_enable(xch, domain_id, evtchn_port);
    if ( rc != 0 )
    {
        switch ( errno ) {
            case EBUSY:
                ERROR("mempaging is (or was) active on this domain");
                break;
            case ENODEV:
                ERROR("mempaging requires Hardware Assisted Paging");
                break;
            case EMLINK:
                ERROR("mempaging not supported while iommu passthrough is enabled");
                break;
            case EXDEV:
                ERROR("mempaging not supported in a PoD guest");
                break;
            default:
                PERROR("mempaging: error initialising shared page");
                break;
        }
        return -1;
    }

    /* Bind event notification */
    rc = xc_evtchn_bind_interdomain(xce_handle, domain_id, *evtchn_port);
    if ( rc < 0 )
    {
        PERROR("Failed to bind event channel");
        return -1;
    }
    *port = rc;

    /* Initialise ring */
    SHARED_RING_INIT((mem_event_sring_t *)ring_page);
    BACK_RING_INIT(back_ring, (mem_event_sring_t *)ring_page, PAGE_SIZE);

    /* Now that the ring is set, remove it from the guest's physmap */
    if ( xc_domain_decrease_reservation_exact(xch, domain_id, 1, 0, &ring_pfn) )
    {
        PERROR("Failed to remove ring_pfn from guest physmap");
        return -1;
    }

    return 0;
}

/*
 * Mem paging ring and event channel teardown routine.
 * The function call invalidates the arguments ring_page and port.
 * The function will return zero on successful completion and will
 * return -1 on failure at any intermediate step setting up errno
 * properly.
 */
int xc_mem_paging_ring_teardown(xc_interface *xch,
                                 xc_evtchn *xce_handle,
                                 domid_t domain_id,
                                 void *ring_page,
                                 int *port)
{
    int rc;

    /* Remove the ring page. */
    rc = munmap(ring_page, PAGE_SIZE);
    if ( rc < 0 )
        PERROR("Error while disabling paging in xen");
    else
        DPRINTF("successfully unmapped ringpage");

    ring_page = NULL;

    /*Disable memory paging. */
    rc = xc_mem_paging_disable(xch, domain_id);
    if ( rc < 0 )
    {
        PERROR("Error while disabling paging in xen");
        goto out;
    }
    else
        DPRINTF("successfully disabled mempaging");

    /* Unbind the event channel. */
    rc = xc_evtchn_unbind(xce_handle, *port);
    if ( rc < 0 )
    {
        PERROR("Error unbinding event port");
        goto out;
    }
    else
        DPRINTF("successfully unbinded event channel");

    /* Set the port to invalid. */
    *port = -1;

    out:
        return rc;
}

/*
 * Local variables:
 * mode: C
 * c-file-style: "BSD"
 * c-basic-offset: 4
 * indent-tabs-mode: nil
 * End:
 */
