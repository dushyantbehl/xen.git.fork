/******************************************************************************
 *
 * tools/libxc/xc_mem_paging.c
 *
 * Interface to low-level memory paging functionality.
 *
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

#include "xc_private.h"

/*
 * Enables mem_paging and sets arg ring page equal to mapped page.
 * Will return 0 on success and -errno on error.
 */
int xc_mem_paging_enable(xc_interface *xch, domid_t domain_id,
                         uint32_t *port,  void *ring_page,
                         mem_event_back_ring_t *back_ring)
{
    return xc_mem_event_enable(xch, domain_id,
                               HVM_PARAM_PAGING_RING_PFN,
                               port, ring_page, back_ring);
}

/*
 * Disable mem_paging and unmap ring page.
 * Will return 0 on success and -errno on error.
 */
int xc_mem_paging_disable(xc_interface *xch, domid_t domain_id, void *ring_page)
{
    return xc_mem_event_teardown(xch, domain_id,
                                 HVM_PARAM_ACCESS_RING_PFN,
                                 ring_page);
}

int xc_mem_paging_nominate(xc_interface *xch, domid_t domain_id, unsigned long gfn)
{
    return xc_mem_event_memop(xch, domain_id,
                                XENMEM_paging_op_nominate,
                                XENMEM_paging_op,
                                gfn, NULL);
}

int xc_mem_paging_evict(xc_interface *xch, domid_t domain_id, unsigned long gfn)
{
    return xc_mem_event_memop(xch, domain_id,
                                XENMEM_paging_op_evict,
                                XENMEM_paging_op,
                                gfn, NULL);
}

int xc_mem_paging_prep(xc_interface *xch, domid_t domain_id, unsigned long gfn)
{
    return xc_mem_event_memop(xch, domain_id,
                                XENMEM_paging_op_prep,
                                XENMEM_paging_op,
                                gfn, NULL);
}

int xc_mem_paging_load(xc_interface *xch, domid_t domain_id, 
                                unsigned long gfn, void *buffer)
{
    int rc, old_errno;

    errno = EINVAL;

    if ( !buffer )
        return -1;

    if ( ((unsigned long) buffer) & (XC_PAGE_SIZE - 1) )
        return -1;

    if ( mlock(buffer, XC_PAGE_SIZE) )
        return -1;
        
    rc = xc_mem_event_memop(xch, domain_id,
                                XENMEM_paging_op_prep,
                                XENMEM_paging_op,
                                gfn, buffer);

    old_errno = errno;
    munlock(buffer, XC_PAGE_SIZE);
    errno = old_errno;

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
