/******************************************************************************
 * xc_domain_restore.c
 *
 * Restore the state of a guest session.
 *
 * Copyright (c) 2003, K A Fraser.
 * Copyright (c) 2006, Intel Corporation
 * Copyright (c) 2007, XenSource Inc.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation;
 * version 2.1 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

/*
 * The superpages flag in restore has two different meanings depending on
 * the type of domain.
 *
 * For an HVM domain, the flag means to look for properly aligned contiguous
 * pages and try to allocate a superpage to satisfy it.  If that fails,
 * fall back to small pages.
 *
 * For a PV domain, the flag means allocate all memory as superpages.  If that
 * fails, the restore fails.  This behavior is required for PV guests who
 * want to use superpages.
 */

#include <stdlib.h>
#include <unistd.h>
#include <inttypes.h>
#include <poll.h>
#include <sys/wait.h>

#include "xg_private.h"
#include "xg_save_restore.h"
#include "xc_dom.h"
#include "xc_bitops.h"
#include "hashtable.h"

#include <xen/hvm/ioreq.h>
#include <xen/hvm/params.h>
#include <xen/event_channel.h>
#include <xen/mem_event.h>

struct restore_ctx {
    unsigned long max_mfn; /* max mfn of the current host machine */
    unsigned long hvirt_start; /* virtual starting address of the hypervisor */
    unsigned int pt_levels; /* #levels of page tables used by the current guest */
    unsigned long nr_pfns; /* number of 'in use' pfns in the guest (i.e. #P2M entries with a valid mfn) */
    xen_pfn_t *live_p2m; /* Live mapping of the table mapping each PFN to its current MFN. */
    xen_pfn_t *p2m; /* A table mapping each PFN to its new MFN. */
    xen_pfn_t *p2m_batch; /* A table of P2M mappings in the current region.  */
    xen_pfn_t *p2m_saved_batch; /* Copy of p2m_batch array for pv superpage alloc */
    int superpages; /* Superpage allocation has been requested */
    int hvm;    /* This is an hvm domain */
    int lazy;   /* To use lazy restore or not. */
    int completed; /* Set when a consistent image is available */
    int last_checkpoint; /* Set when we should commit to the current checkpoint when it completes. */
    int compressing; /* Set when sender signals that pages would be sent compressed (for Remus) */
    struct domain_info_context dinfo;
    int pager_fallback; /* Set when lazy restore pager fails to setup and we fallback to normal restore.*/
};

struct mem_event {
    domid_t domain_id;
    xc_evtchn *xce_handle;
    int port;
    mem_event_back_ring_t back_ring;
    uint32_t evtchn_port;
    void *ring_page;
};

/* The domain-id of the new domain is written to the path at %u */
#define XC_LAZY_RESTORE_PAGER_LOG_FILE "/var/log/xen/lazy_restore_pager_domain_%u"
#define LAZY_RESTORE_PAGER_SUCCESS "setup-success"
#define LAZY_RESTORE_PAGER_FAILURE "setup-failure"

/*
 * hash_from_key_fn and keys_equal_fn.
 * functions used by hash function to hash pfn's.
 * Copied directly from tools/xenstore/xenstore_code.h
 * Currently no modification, Will modify later if required.
 */
static inline unsigned int hash_from_key_fn(void *k)
{
    char *str = k;
    unsigned int hash = 5381;
    char c;

    while ((c = *str++))
        hash = ((hash << 5) + hash) + (unsigned int)c;

    return hash;
}

static inline int keys_equal_fn(void *key1, void *key2)
{
    return 0 == strcmp((char *)key1, (char *)key2);
}

/* Define the hashtable insert, search and remove functions. */
DEFINE_HASHTABLE_INSERT_VALUE(hashtable_insert_pfn, uint64_t, off_t);
DEFINE_HASHTABLE_REMOVE(hashtable_remove_pfn, uint64_t, off_t)
DEFINE_HASHTABLE_SEARCH(hashtable_search_pfn, uint64_t, off_t)

#define HEARTBEAT_MS 1000

#ifndef __MINIOS__
static ssize_t rdexact(xc_interface *xch, struct restore_ctx *ctx,
                       int fd, void* buf, size_t size)
{
    size_t offset = 0;
    ssize_t len;
    struct timeval tv;
    fd_set rfds;

    while ( offset < size )
    {
        if ( ctx->completed ) {
            /* expect a heartbeat every HEARBEAT_MS ms maximum */
            tv.tv_sec = HEARTBEAT_MS / 1000;
            tv.tv_usec = (HEARTBEAT_MS % 1000) * 1000;

            FD_ZERO(&rfds);
            FD_SET(fd, &rfds);
            len = select(fd + 1, &rfds, NULL, NULL, &tv);
            if ( len == -1 && errno == EINTR )
                continue;
            if ( !FD_ISSET(fd, &rfds) ) {
                ERROR("%s failed (select returned %zd)", __func__, len);
                errno = ETIMEDOUT;
                return -1;
            }
        }

        len = read(fd, buf + offset, size - offset);
        if ( (len == -1) && ((errno == EINTR) || (errno == EAGAIN)) )
            continue;
        if ( len == 0 ) {
            ERROR("0-length read");
            errno = 0;
        }
        if ( len <= 0 ) {
            ERROR("%s failed (read rc: %zd, errno: %d)", __func__, len, errno);
            return -1;
        }
        offset += len;
    }

    return 0;
}

#define RDEXACT(fd,buf,size) rdexact(xch, ctx, fd, buf, size)
#else
#define RDEXACT read_exact
#endif

#define SUPERPAGE_PFN_SHIFT  9
#define SUPERPAGE_NR_PFNS    (1UL << SUPERPAGE_PFN_SHIFT)
#define SUPERPAGE(_pfn) ((_pfn) & (~(SUPERPAGE_NR_PFNS-1)))
#define SUPER_PAGE_START(pfn)    (((pfn) & (SUPERPAGE_NR_PFNS-1)) == 0 )

/*
** When we're restoring into a pv superpage-allocated guest, we take
** a copy of the p2m_batch array to preserve the pfn, then allocate the
** corresponding superpages.  We then fill in the p2m array using the saved
** pfns.
*/
static int alloc_superpage_mfns(
    xc_interface *xch, uint32_t dom, struct restore_ctx *ctx, int nr_mfns)
{
    int i, j, max = 0;
    unsigned long pfn, base_pfn, mfn;

    for (i = 0; i < nr_mfns; i++)
    {
        pfn = ctx->p2m_batch[i];
        base_pfn = SUPERPAGE(pfn);
        if (ctx->p2m[base_pfn] != (INVALID_P2M_ENTRY-2))
        {
            ctx->p2m_saved_batch[max] = base_pfn;
            ctx->p2m_batch[max] = base_pfn;
            max++;
            ctx->p2m[base_pfn] = INVALID_P2M_ENTRY-2;
        }
    }
    if (xc_domain_populate_physmap_exact(xch, dom, max, SUPERPAGE_PFN_SHIFT,
                                         0, ctx->p2m_batch) != 0)
        return 1;

    for (i = 0; i < max; i++)
    {
        mfn = ctx->p2m_batch[i];
        pfn = ctx->p2m_saved_batch[i];
        for (j = 0; j < SUPERPAGE_NR_PFNS; j++)
            ctx->p2m[pfn++] = mfn++;
    }
    return 0;
}
/*
** In the state file (or during transfer), all page-table pages are
** converted into a 'canonical' form where references to actual mfns
** are replaced with references to the corresponding pfns.
** This function inverts that operation, replacing the pfn values with
** the (now known) appropriate mfn values.
*/
static int uncanonicalize_pagetable(
    xc_interface *xch, uint32_t dom, struct restore_ctx *ctx, void *page)
{
    int i, rc, pte_last, nr_mfns = 0;
    unsigned long pfn;
    uint64_t pte;
    struct domain_info_context *dinfo = &ctx->dinfo;

    pte_last = PAGE_SIZE / 8;

    /* First pass: work out how many (if any) MFNs we need to alloc */
    for ( i = 0; i < pte_last; i++ )
    {
        pte = ((uint64_t *)page)[i];

        /* XXX SMH: below needs fixing for PROT_NONE etc */
        if ( !(pte & _PAGE_PRESENT) )
            continue;
        
        pfn = (pte >> PAGE_SHIFT) & MFN_MASK_X86;
        
        if ( pfn >= dinfo->p2m_size )
        {
            /* This "page table page" is probably not one; bail. */
            ERROR("Frame number in page table is out of range: "
                  "i=%d pfn=0x%lx p2m_size=%lu",
                  i, pfn, dinfo->p2m_size);
            return 0;
        }
        
        if ( ctx->p2m[pfn] == INVALID_P2M_ENTRY )
        {
            /* Have a 'valid' PFN without a matching MFN - need to alloc */
            ctx->p2m_batch[nr_mfns++] = pfn; 
            ctx->p2m[pfn]--;
        }
    }

    /* Allocate the requisite number of mfns. */
    if (nr_mfns)
    {
        if (!ctx->hvm && ctx->superpages)
            rc = alloc_superpage_mfns(xch, dom, ctx, nr_mfns);
        else
            rc = xc_domain_populate_physmap_exact(xch, dom, nr_mfns, 0, 0,
                                                  ctx->p2m_batch);

        if (rc)
        {
            ERROR("Failed to allocate memory for batch.!\n");
            errno = ENOMEM;
            return 0;
        }
    }
    
    /* Second pass: uncanonicalize each present PTE */
    nr_mfns = 0;
    for ( i = 0; i < pte_last; i++ )
    {
        pte = ((uint64_t *)page)[i];
        
        /* XXX SMH: below needs fixing for PROT_NONE etc */
        if ( !(pte & _PAGE_PRESENT) )
            continue;
        
        pfn = (pte >> PAGE_SHIFT) & MFN_MASK_X86;

        if ( ctx->p2m[pfn] == (INVALID_P2M_ENTRY-1) )
            ctx->p2m[pfn] = ctx->p2m_batch[nr_mfns++];

        pte &= ~MADDR_MASK_X86;
        pte |= (uint64_t)ctx->p2m[pfn] << PAGE_SHIFT;

        ((uint64_t *)page)[i] = (uint64_t)pte;
    }

    return 1;
}


/* Load the p2m frame list, plus potential extended info chunk */
static xen_pfn_t *load_p2m_frame_list(
    xc_interface *xch, struct restore_ctx *ctx,
    int io_fd, int *pae_extended_cr3, int *ext_vcpucontext,
    uint32_t *vcpuextstate_size)
{
    xen_pfn_t *p2m_frame_list;
    vcpu_guest_context_any_t ctxt;
    xen_pfn_t p2m_fl_zero;
    struct domain_info_context *dinfo = &ctx->dinfo;

    /* Read first entry of P2M list, or extended-info signature (~0UL). */
    if ( RDEXACT(io_fd, &p2m_fl_zero, sizeof(long)) )
    {
        PERROR("read extended-info signature failed");
        return NULL;
    }
    
    if ( p2m_fl_zero == ~0UL )
    {
        uint32_t tot_bytes;
        
        /* Next 4 bytes: total size of following extended info. */
        if ( RDEXACT(io_fd, &tot_bytes, sizeof(tot_bytes)) )
        {
            PERROR("read extended-info size failed");
            return NULL;
        }
        
        while ( tot_bytes )
        {
            uint32_t chunk_bytes;
            char     chunk_sig[4];
            
            /* 4-character chunk signature + 4-byte remaining chunk size. */
            if ( RDEXACT(io_fd, chunk_sig, sizeof(chunk_sig)) ||
                 RDEXACT(io_fd, &chunk_bytes, sizeof(chunk_bytes)) ||
                 (tot_bytes < (chunk_bytes + 8)) )
            {
                PERROR("read extended-info chunk signature failed");
                return NULL;
            }
            tot_bytes -= 8;

            /* VCPU context structure? */
            if ( !strncmp(chunk_sig, "vcpu", 4) )
            {
                /* Pick a guest word-size and PT depth from the ctxt size */
                if ( chunk_bytes == sizeof (ctxt.x32) )
                {
                    dinfo->guest_width = 4;
                    ctx->pt_levels = 3;
                }
                else if ( chunk_bytes == sizeof (ctxt.x64) )
                {
                    dinfo->guest_width = 8;
                    ctx->pt_levels = 4;
                }
                else 
                {
                    ERROR("bad extended-info context size %d", chunk_bytes);
                    return NULL;
                }

                if ( RDEXACT(io_fd, &ctxt, chunk_bytes) )
                {
                    PERROR("read extended-info vcpu context failed");
                    return NULL;
                }
                tot_bytes -= chunk_bytes;
                chunk_bytes = 0;

                if ( GET_FIELD(&ctxt, vm_assist, dinfo->guest_width)
                     & (1UL << VMASST_TYPE_pae_extended_cr3) )
                    *pae_extended_cr3 = 1;
            }
            else if ( !strncmp(chunk_sig, "extv", 4) )
            {
                *ext_vcpucontext = 1;
            }
            else if ( !strncmp(chunk_sig, "xcnt", 4) )
            {
                if ( RDEXACT(io_fd, vcpuextstate_size, sizeof(*vcpuextstate_size)) )
                {
                    PERROR("read extended vcpu state size failed");
                    return NULL;
                }
                tot_bytes -= chunk_bytes;
                chunk_bytes = 0;
            }
            
            /* Any remaining bytes of this chunk: read and discard. */
            while ( chunk_bytes )
            {
                unsigned long sz = min_t(unsigned long, chunk_bytes, sizeof(xen_pfn_t));
                if ( RDEXACT(io_fd, &p2m_fl_zero, sz) )
                {
                    PERROR("read-and-discard extended-info chunk bytes failed");
                    return NULL;
                }
                chunk_bytes -= sz;
                tot_bytes   -= sz;
            }
        }

        /* Now read the real first entry of P2M list. */
        if ( RDEXACT(io_fd, &p2m_fl_zero, sizeof(xen_pfn_t)) )
        {
            PERROR("read first entry of p2m_frame_list failed");
            return NULL;
        }
    }

    /* Now that we know the guest's word-size, can safely allocate 
     * the p2m frame list */
    if ( (p2m_frame_list = malloc(P2M_TOOLS_FL_SIZE)) == NULL )
    {
        ERROR("Couldn't allocate p2m_frame_list array");
        return NULL;
    }

    /* First entry has already been read. */
    p2m_frame_list[0] = p2m_fl_zero;
    if ( RDEXACT(io_fd, &p2m_frame_list[1], 
                 (P2M_FL_ENTRIES - 1) * sizeof(xen_pfn_t)) )
    {
        PERROR("read p2m_frame_list failed");
        free(p2m_frame_list);
        return NULL;
    }
    
    return p2m_frame_list;
}

typedef struct {
    int ishvm;
    union {
        struct tailbuf_pv {
            unsigned int pfncount;
            unsigned long* pfntab;
            unsigned int vcpucount;
            unsigned char* vcpubuf;
            unsigned char shared_info_page[PAGE_SIZE];
        } pv;
        struct tailbuf_hvm {
            uint64_t magicpfns[3];
            uint32_t hvmbufsize, reclen;
            uint8_t* hvmbuf;
            struct {
                uint32_t magic;
                uint32_t version;
                uint64_t len;
            } qemuhdr;
            uint32_t qemubufsize;
            uint8_t* qemubuf;
        } hvm;
    } u;
} tailbuf_t;

/* read stream until EOF, growing buffer as necssary */
static int compat_buffer_qemu(xc_interface *xch, struct restore_ctx *ctx,
                              int fd, struct tailbuf_hvm *buf)
{
    uint8_t *qbuf, *tmp;
    int blen = 0, dlen = 0;
    int rc;

    /* currently save records tend to be about 7K */
    blen = 8192;
    if ( !(qbuf = malloc(blen)) ) {
        ERROR("Error allocating QEMU buffer");
        return -1;
    }

    while( (rc = read(fd, qbuf+dlen, blen-dlen)) > 0 ) {
        DPRINTF("Read %d bytes of QEMU data\n", rc);
        dlen += rc;

        if (dlen == blen) {
            DPRINTF("%d-byte QEMU buffer full, reallocating...\n", dlen);
            blen += 4096;
            tmp = realloc(qbuf, blen);
            if ( !tmp ) {
                ERROR("Error growing QEMU buffer to %d bytes", blen);
                free(qbuf);
                return -1;
            }
            qbuf = tmp;
        }
    }

    if ( rc < 0 ) {
        ERROR("Error reading QEMU data");
        free(qbuf);
        return -1;
    }

    if ( memcmp(qbuf, "QEVM", 4) ) {
        ERROR("Invalid QEMU magic: 0x%08"PRIx32, *(uint32_t*)qbuf);
        free(qbuf);
        return -1;
    }

    buf->qemubuf = qbuf;
    buf->qemubufsize = dlen;

    return 0;
}

static int buffer_qemu(xc_interface *xch, struct restore_ctx *ctx,
                       int fd, struct tailbuf_hvm *buf)
{
    uint32_t qlen;
    uint8_t *tmp;

    if ( RDEXACT(fd, &qlen, sizeof(qlen)) ) {
        PERROR("Error reading QEMU header length");
        return -1;
    }

    if ( qlen > buf->qemubufsize ) {
        if ( buf->qemubuf) {
            tmp = realloc(buf->qemubuf, qlen);
            if ( tmp )
                buf->qemubuf = tmp;
            else {
                ERROR("Error reallocating QEMU state buffer");
                return -1;
            }
        } else {
            buf->qemubuf = malloc(qlen);
            if ( !buf->qemubuf ) {
                ERROR("Error allocating QEMU state buffer");
                return -1;
            }
        }
    }
    buf->qemubufsize = qlen;

    if ( RDEXACT(fd, buf->qemubuf, buf->qemubufsize) ) {
        PERROR("Error reading QEMU state");
        return -1;
    }

    return 0;
}

static int dump_qemu(xc_interface *xch, uint32_t dom, struct tailbuf_hvm *buf)
{
    int saved_errno;
    char path[256];
    FILE *fp;

    sprintf(path, XC_DEVICE_MODEL_RESTORE_FILE".%u", dom);
    fp = fopen(path, "wb");
    if ( !fp )
        return -1;

    DPRINTF("Writing %d bytes of QEMU data\n", buf->qemubufsize);
    if ( fwrite(buf->qemubuf, 1, buf->qemubufsize, fp) != buf->qemubufsize) {
        saved_errno = errno;
        fclose(fp);
        errno = saved_errno;
        return -1;
    }

    fclose(fp);

    return 0;
}

static int buffer_tail_hvm(xc_interface *xch, struct restore_ctx *ctx,
                           struct tailbuf_hvm *buf, int fd,
                           unsigned int max_vcpu_id, uint64_t *vcpumap,
                           int ext_vcpucontext,
                           uint32_t vcpuextstate_size)
{
    uint8_t *tmp;
    unsigned char qemusig[21];

    if ( RDEXACT(fd, buf->magicpfns, sizeof(buf->magicpfns)) ) {
        PERROR("Error reading magic PFNs");
        return -1;
    }

    if ( RDEXACT(fd, &buf->reclen, sizeof(buf->reclen)) ) {
        PERROR("Error reading HVM params size");
        return -1;
    }

    if ( buf->reclen > buf->hvmbufsize ) {
        if ( buf->hvmbuf) {
            tmp = realloc(buf->hvmbuf, buf->reclen);
            if ( tmp ) {
                buf->hvmbuf = tmp;
                buf->hvmbufsize = buf->reclen;
            } else {
                ERROR("Error reallocating HVM param buffer");
                return -1;
            }
        } else {
            buf->hvmbuf = malloc(buf->reclen);
            if ( !buf->hvmbuf ) {
                ERROR("Error allocating HVM param buffer");
                return -1;
            }
            buf->hvmbufsize = buf->reclen;
        }
    }

    if ( RDEXACT(fd, buf->hvmbuf, buf->reclen) ) {
        PERROR("Error reading HVM params");
        return -1;
    }

    if ( RDEXACT(fd, qemusig, sizeof(qemusig)) ) {
        PERROR("Error reading QEMU signature");
        return -1;
    }

    /* The legacy live-migration QEMU record has no length information.
     * Short of reimplementing the QEMU parser, we're forced to just read
     * until EOF.
     *
     * Gets around this by sending a different signatures for the new
     * live-migration QEMU record and Remus which includes a length
     * prefix
     */
    if ( !memcmp(qemusig, "QemuDeviceModelRecord", sizeof(qemusig)) )
        return compat_buffer_qemu(xch, ctx, fd, buf);
    else if ( !memcmp(qemusig, "DeviceModelRecord0002", sizeof(qemusig)) ||
              !memcmp(qemusig, "RemusDeviceModelState", sizeof(qemusig)) )
        return buffer_qemu(xch, ctx, fd, buf);

    qemusig[20] = '\0';
    ERROR("Invalid QEMU signature: %s", qemusig);
    return -1;
}

static int buffer_tail_pv(xc_interface *xch, struct restore_ctx *ctx,
                          struct tailbuf_pv *buf, int fd,
                          unsigned int max_vcpu_id, uint64_t *vcpumap,
                          int ext_vcpucontext,
                          uint32_t vcpuextstate_size)
{
    unsigned int i;
    size_t pfnlen, vcpulen;
    struct domain_info_context *dinfo = &ctx->dinfo;

    /* TODO: handle changing pfntab and vcpu counts */
    /* PFN tab */
    if ( RDEXACT(fd, &buf->pfncount, sizeof(buf->pfncount)) ||
         (buf->pfncount > (1U << 28)) ) /* up to 1TB of address space */
    {
        PERROR("Error when reading pfn count");
        return -1;
    }
    pfnlen = sizeof(unsigned long) * buf->pfncount;
    if ( !(buf->pfntab) ) {
        if ( !(buf->pfntab = malloc(pfnlen)) ) {
            ERROR("Error allocating PFN tail buffer");
            return -1;
        }
    }
    // DPRINTF("Reading PFN tab: %d bytes\n", pfnlen);
    if ( RDEXACT(fd, buf->pfntab, pfnlen) ) {
        PERROR("Error when reading pfntab");
        goto free_pfntab;
    }

    /* VCPU contexts */
    buf->vcpucount = 0;
    for (i = 0; i <= max_vcpu_id; i++) {
        // DPRINTF("vcpumap: %llx, cpu: %d, bit: %llu\n", vcpumap[i/64], i, (vcpumap[i/64] & (1ULL << (i%64))));
        if ( (!(vcpumap[i/64] & (1ULL << (i%64)))) )
            continue;
        buf->vcpucount++;
    }
    // DPRINTF("VCPU count: %d\n", buf->vcpucount);
    vcpulen = ((dinfo->guest_width == 8) ? sizeof(vcpu_guest_context_x86_64_t)
               : sizeof(vcpu_guest_context_x86_32_t)) * buf->vcpucount;
    if ( ext_vcpucontext )
        vcpulen += 128 * buf->vcpucount;
    vcpulen += vcpuextstate_size * buf->vcpucount;

    if ( !(buf->vcpubuf) ) {
        if ( !(buf->vcpubuf = malloc(vcpulen)) ) {
            ERROR("Error allocating VCPU ctxt tail buffer");
            goto free_pfntab;
        }
    }
    // DPRINTF("Reading VCPUS: %d bytes\n", vcpulen);
    if ( RDEXACT(fd, buf->vcpubuf, vcpulen) ) {
        PERROR("Error when reading ctxt");
        goto free_vcpus;
    }

    /* load shared_info_page */
    // DPRINTF("Reading shared info: %lu bytes\n", PAGE_SIZE);
    if ( RDEXACT(fd, buf->shared_info_page, PAGE_SIZE) ) {
        PERROR("Error when reading shared info page");
        goto free_vcpus;
    }

    return 0;

  free_vcpus:
    if (buf->vcpubuf) {
        free (buf->vcpubuf);
        buf->vcpubuf = NULL;
    }
  free_pfntab:
    if (buf->pfntab) {
        free (buf->pfntab);
        buf->pfntab = NULL;
    }

    return -1;
}

static int buffer_tail(xc_interface *xch, struct restore_ctx *ctx,
                       tailbuf_t *buf, int fd, unsigned int max_vcpu_id,
                       uint64_t *vcpumap, int ext_vcpucontext,
                       uint32_t vcpuextstate_size)
{
    if ( buf->ishvm )
        return buffer_tail_hvm(xch, ctx, &buf->u.hvm, fd, max_vcpu_id, vcpumap,
                               ext_vcpucontext, vcpuextstate_size);
    else
        return buffer_tail_pv(xch, ctx, &buf->u.pv, fd, max_vcpu_id, vcpumap,
                              ext_vcpucontext, vcpuextstate_size);
}

static void tailbuf_free_hvm(struct tailbuf_hvm *buf)
{
    if ( buf->hvmbuf ) {
        free(buf->hvmbuf);
        buf->hvmbuf = NULL;
    }
    if ( buf->qemubuf ) {
        free(buf->qemubuf);
        buf->qemubuf = NULL;
    }
}

static void tailbuf_free_pv(struct tailbuf_pv *buf)
{
    if ( buf->vcpubuf ) {
        free(buf->vcpubuf);
        buf->vcpubuf = NULL;
    }
    if ( buf->pfntab ) {
        free(buf->pfntab);
        buf->pfntab = NULL;
    }
}

static void tailbuf_free(tailbuf_t *buf)
{
    if ( buf->ishvm )
        tailbuf_free_hvm(&buf->u.hvm);
    else
        tailbuf_free_pv(&buf->u.pv);
}

struct toolstack_data_t {
    uint8_t *data;
    uint32_t len;
};

typedef struct {
    void* pages;
    /* pages is of length nr_physpages, pfn_types is of length nr_pages */
    unsigned int nr_physpages, nr_pages, total_pages;

    /* checkpoint compression state */
    int compressing;
    unsigned long compbuf_pos, compbuf_size;

    /* Types of the pfns in the current region */
    unsigned long* pfn_types;

    /*Hashtable storing pfn to fileoffset map for lazy restore.*/
    struct hashtable *pfn_to_fileoffset;

    int verify;

    int new_ctxt_format;
    int max_vcpu_id;
    uint64_t vcpumap[XC_SR_MAX_VCPUS/64];
    uint64_t identpt;
    uint64_t paging_ring_pfn;
    uint64_t access_ring_pfn;
    uint64_t sharing_ring_pfn;
    uint64_t vm86_tss;
    uint64_t console_pfn;
    uint64_t acpi_ioport_location;
    uint64_t viridian;
    uint64_t vm_generationid_addr;
    uint64_t ioreq_server_pfn;
    uint64_t nr_ioreq_server_pages;

    struct toolstack_data_t tdata;
} pagebuf_t;

static int pagebuf_init(pagebuf_t* buf)
{
    memset(buf, 0, sizeof(*buf));
    return 0;
}

static void pagebuf_free(pagebuf_t* buf)
{
    if (buf->tdata.data != NULL) {
        free(buf->tdata.data);
        buf->tdata.data = NULL;
    }
    if (buf->pages) {
        free(buf->pages);
        buf->pages = NULL;
    }
    if(buf->pfn_types) {
        free(buf->pfn_types);
        buf->pfn_types = NULL;
    }
    if(buf->pfn_to_fileoffset) {
        /* Tell hashtable to free the values too. */
        hashtable_destroy(buf->pfn_to_fileoffset,1);
        buf->pfn_to_fileoffset = NULL;
    }
}

/* Function to perform libxl callback */
static inline int do_callback(xc_interface *xch, uint32_t dom,
                       struct toolstack_data_t *tdata,
                       struct restore_callbacks *callbacks)
{
    int rc = 0;
    if ( tdata && tdata->data != NULL )
    {
        if ( callbacks != NULL && callbacks->toolstack_restore != NULL )
        {
            DPRINTF("Going to call callback function");
            rc = callbacks->toolstack_restore(dom, tdata->data, tdata->len,
                                               callbacks->data);
            free(tdata->data);
            if ( rc < 0 )
                PERROR("error calling toolstack_restore");
        }
        else
        {
            rc = -1;
            ERROR("toolstack data available but no callback provided\n");
            free(tdata->data);
        }
    }
    return rc;
}

static int nominate_and_evict_one(xc_interface *xch, uint32_t dom,
                                  unsigned long _pfn)
{
    int rc;
    unsigned long pfn = _pfn;

    /* Nominate page */
    rc = xc_mem_paging_nominate(xch, dom, pfn);
    if ( rc < 0 )
    {
        /* unpageable gfn is indicated by EBUSY */
        if ( errno == EBUSY )
            rc = errno;
        else
        {
            PERROR("Error nominating page %lx", pfn);
            rc = -errno;
        }
        goto out;
    }

    /* Tell Xen to evict page */
    rc = xc_mem_paging_evict(xch, dom, pfn);
    if ( rc < 0 )
    {
        /* A gfn in use is indicated by EBUSY */
        if ( errno == EBUSY )
        {
            DPRINTF("Nominated page %lx busy, How is this possible", pfn);
        } else
            PERROR("Error evicting page %lx", pfn);
        rc = -errno;
        goto out;
    }

    rc = 0;
    out:
        return rc;
}

static int nominate_and_evict(xc_interface *xch, struct restore_ctx *ctx,
                              pagebuf_t* buf, tailbuf_t *tailbuf, uint32_t dom)
{
    int i, rc = 0;
    unsigned long pfn;
    uint32_t unpageable = 0;

    for ( i=0; i<buf->total_pages; i++ )
    {
        pfn = buf->pfn_types[i] ;

        if (pfn == tailbuf->u.hvm.magicpfns[0] ||
            pfn == tailbuf->u.hvm.magicpfns[1] ||
            pfn == tailbuf->u.hvm.magicpfns[2] )
        {
            DPRINTF("Skipping magic pfn %lx",pfn);
            continue;
        }

        if (pfn == buf->console_pfn      ||
            pfn == buf->paging_ring_pfn  ||
            pfn == buf->access_ring_pfn  ||
            pfn == buf->sharing_ring_pfn ||
            pfn == buf->ioreq_server_pfn  )
        {
            DPRINTF("Skipping usual pfn %lx",pfn);
            continue;
        }

        rc = nominate_and_evict_one(xch, dom, pfn);
        if ( rc == EBUSY )
        {
            unpageable++;
            continue;
        }
        if( rc < 0)
        {
            PERROR("Could not evict page %d, pfn - %lx",i,pfn);
            goto out;
        }
    }
    DPRINTF("restore-pager: nominate and evict pfn's done\n"
            "\ttotal pages - %u and unpageable pages %u",buf->total_pages,unpageable);

  out:
    return rc;
}

static int pagebuf_get_one(xc_interface *xch, struct restore_ctx *ctx,
                           pagebuf_t* buf, int fd, uint32_t dom)
{
    int count, countpages, oldcount, i;
    void* ptmp;
    unsigned long compbuf_size;
    unsigned long  pagetype=0;

    if ( RDEXACT(fd, &count, sizeof(count)) )
    {
        PERROR("Error when reading batch size");
        return -1;
    }

    // DPRINTF("reading batch of %d pages\n", count);

    switch ( count )
    {
    case 0:
        // DPRINTF("Last batch read\n");
        return 0;

    case XC_SAVE_ID_ENABLE_VERIFY_MODE:
        DPRINTF("Entering page verify mode\n");
        buf->verify = 1;
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_VCPU_INFO:
        buf->new_ctxt_format = 1;
        if ( RDEXACT(fd, &buf->max_vcpu_id, sizeof(buf->max_vcpu_id)) ||
             buf->max_vcpu_id >= XC_SR_MAX_VCPUS ||
             RDEXACT(fd, buf->vcpumap, vcpumap_sz(buf->max_vcpu_id)) ) {
            PERROR("Error when reading max_vcpu_id");
            return -1;
        }
        // DPRINTF("Max VCPU ID: %d, vcpumap: %llx\n", buf->max_vcpu_id, buf->vcpumap[0]);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_IDENT_PT:
        /* Skip padding 4 bytes then read the EPT identity PT location. */
        if ( RDEXACT(fd, &buf->identpt, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->identpt, sizeof(uint64_t)) )
        {
            PERROR("error read the address of the EPT identity map");
            return -1;
        }
        // DPRINTF("EPT identity map address: %llx\n", buf->identpt);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_PAGING_RING_PFN:
        /* Skip padding 4 bytes then read the paging ring location. */
        if ( RDEXACT(fd, &buf->paging_ring_pfn, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->paging_ring_pfn, sizeof(uint64_t)) )
        {
            PERROR("error read the paging ring pfn");
            return -1;
        }
        // DPRINTF("paging ring pfn address: %llx\n", buf->paging_ring_pfn);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_ACCESS_RING_PFN:
        /* Skip padding 4 bytes then read the mem access ring location. */
        if ( RDEXACT(fd, &buf->access_ring_pfn, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->access_ring_pfn, sizeof(uint64_t)) )
        {
            PERROR("error read the access ring pfn");
            return -1;
        }
        // DPRINTF("access ring pfn address: %llx\n", buf->access_ring_pfn);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_SHARING_RING_PFN:
        /* Skip padding 4 bytes then read the sharing ring location. */
        if ( RDEXACT(fd, &buf->sharing_ring_pfn, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->sharing_ring_pfn, sizeof(uint64_t)) )
        {
            PERROR("error read the sharing ring pfn");
            return -1;
        }
        // DPRINTF("sharing ring pfn address: %llx\n", buf->sharing_ring_pfn);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_VM86_TSS:
        /* Skip padding 4 bytes then read the vm86 TSS location. */
        if ( RDEXACT(fd, &buf->vm86_tss, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->vm86_tss, sizeof(uint64_t)) )
        {
            PERROR("error read the address of the vm86 TSS");
            return -1;
        }
        // DPRINTF("VM86 TSS location: %llx\n", buf->vm86_tss);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_TMEM:
        DPRINTF("xc_domain_restore start tmem\n");
        if ( xc_tmem_restore(xch, dom, fd) ) {
            PERROR("error reading/restoring tmem");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_TMEM_EXTRA:
        if ( xc_tmem_restore_extra(xch, dom, fd) ) {
            PERROR("error reading/restoring tmem extra");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_TSC_INFO:
    {
        uint32_t tsc_mode, khz, incarn;
        uint64_t nsec;
        if ( RDEXACT(fd, &tsc_mode, sizeof(uint32_t)) ||
             RDEXACT(fd, &nsec, sizeof(uint64_t)) ||
             RDEXACT(fd, &khz, sizeof(uint32_t)) ||
             RDEXACT(fd, &incarn, sizeof(uint32_t)) ||
             xc_domain_set_tsc_info(xch, dom, tsc_mode, nsec, khz, incarn) ) {
            PERROR("error reading/restoring tsc info");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);
    }

    case XC_SAVE_ID_HVM_CONSOLE_PFN :
        /* Skip padding 4 bytes then read the console pfn location. */
        if ( RDEXACT(fd, &buf->console_pfn, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->console_pfn, sizeof(uint64_t)) )
        {
            PERROR("error read the address of the console pfn");
            return -1;
        }
        // DPRINTF("console pfn location: %llx\n", buf->console_pfn);
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_LAST_CHECKPOINT:
        ctx->last_checkpoint = 1;
        // DPRINTF("last checkpoint indication received");
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_ACPI_IOPORTS_LOCATION:
        /* Skip padding 4 bytes then read the acpi ioport location. */
        if ( RDEXACT(fd, &buf->acpi_ioport_location, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->acpi_ioport_location, sizeof(uint64_t)) )
        {
            PERROR("error read the acpi ioport location");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_VIRIDIAN:
        /* Skip padding 4 bytes then read the acpi ioport location. */
        if ( RDEXACT(fd, &buf->viridian, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->viridian, sizeof(uint64_t)) )
        {
            PERROR("error read the viridian flag");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_TOOLSTACK:
        {
            if ( RDEXACT(fd, &buf->tdata.len, sizeof(buf->tdata.len)) )
            {
                PERROR("error read toolstack id size");
                return -1;
            }
            buf->tdata.data = (uint8_t*) realloc(buf->tdata.data, buf->tdata.len);
            if ( buf->tdata.data == NULL )
            {
                PERROR("error memory allocation");
                return -1;
            }
            if ( RDEXACT(fd, buf->tdata.data, buf->tdata.len) )
            {
                PERROR("error read toolstack id");
                return -1;
            }
            return pagebuf_get_one(xch, ctx, buf, fd, dom);
        }

    case XC_SAVE_ID_ENABLE_COMPRESSION:
        /* We cannot set compression flag directly in pagebuf structure,
         * since this pagebuf still has uncompressed pages that are yet to
         * be applied. We enable the compression field in pagebuf structure
         * after receiving the first tailbuf.
         */
        ctx->compressing = 1;
        // DPRINTF("compression flag received");
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_COMPRESSED_DATA:

        /* read the length of compressed chunk coming in */
        if ( RDEXACT(fd, &compbuf_size, sizeof(unsigned long)) )
        {
            PERROR("Error when reading compbuf_size");
            return -1;
        }
        if (!compbuf_size) return 1;

        buf->compbuf_size += compbuf_size;
        if (!(ptmp = realloc(buf->pages, buf->compbuf_size))) {
            ERROR("Could not (re)allocate compression buffer");
            return -1;
        }
        buf->pages = ptmp;

        if ( RDEXACT(fd, buf->pages + (buf->compbuf_size - compbuf_size),
                     compbuf_size) ) {
            PERROR("Error when reading compression buffer");
            return -1;
        }
        return compbuf_size;

    case XC_SAVE_ID_HVM_GENERATION_ID_ADDR:
        /* Skip padding 4 bytes then read the generation id buffer location. */
        if ( RDEXACT(fd, &buf->vm_generationid_addr, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->vm_generationid_addr, sizeof(uint64_t)) )
        {
            PERROR("error read the generation id buffer location");
            return -1;
        }
        DPRINTF("read generation id buffer address");
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_IOREQ_SERVER_PFN:
        /* Skip padding 4 bytes then read the ioreq server gmfn base. */
        if ( RDEXACT(fd, &buf->ioreq_server_pfn, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->ioreq_server_pfn, sizeof(uint64_t)) )
        {
            PERROR("error read the ioreq server gmfn base");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    case XC_SAVE_ID_HVM_NR_IOREQ_SERVER_PAGES:
        /* Skip padding 4 bytes then read the ioreq server gmfn count. */
        if ( RDEXACT(fd, &buf->nr_ioreq_server_pages, sizeof(uint32_t)) ||
             RDEXACT(fd, &buf->nr_ioreq_server_pages, sizeof(uint64_t)) )
        {
            PERROR("error read the ioreq server gmfn count");
            return -1;
        }
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    default:
        if ( (count > MAX_BATCH_SIZE) || (count < 0) ) {
            ERROR("Max batch size exceeded (%d). Giving up.", count);
            errno = EMSGSIZE;
            return -1;
        }
        break;
    }

    oldcount = buf->nr_pages;
    buf->nr_pages += count;
    if (!buf->pfn_types) {
        if (!(buf->pfn_types = malloc(buf->nr_pages * sizeof(*(buf->pfn_types))))) {
            ERROR("Could not allocate PFN type buffer");
            return -1;
        }
    } else {
        if (!(ptmp = realloc(buf->pfn_types, buf->nr_pages * sizeof(*(buf->pfn_types))))) {
            ERROR("Could not reallocate PFN type buffer");
            return -1;
        }
        buf->pfn_types = ptmp;
    }
    if ( RDEXACT(fd, buf->pfn_types + oldcount, count * sizeof(*(buf->pfn_types)))) {
        PERROR("Error when reading region pfn types");
        return -1;
    }

    if ( ctx->lazy )
    {
        int pages_this_batch = 0;
        off_t prev_offset=0, temp_offset=0, page_offset=0;

        prev_offset = lseek(fd, 0, SEEK_CUR);
        if ( prev_offset < 0 )
        {
            PERROR("ERROR problem reading file offset");
            return -errno;
        }

        for (i = oldcount; i < buf->nr_pages; ++i)
        {
            pagetype = buf->pfn_types[i] & XEN_DOMCTL_PFINFO_LTAB_MASK;
            if ( pagetype == XEN_DOMCTL_PFINFO_XTAB ||
                 pagetype == XEN_DOMCTL_PFINFO_BROKEN ||
                 pagetype == XEN_DOMCTL_PFINFO_XALLOC )
            {
                page_offset = (off_t)-1;
            }
            else
            {
                page_offset = prev_offset + pages_this_batch*PAGE_SIZE;
                pages_this_batch++;
            }

            if( ! hashtable_insert_pfn(buf->pfn_to_fileoffset,
                                       &buf->pfn_types[i],
                                       page_offset))
            {
                PERROR("Error Inserting pfn (%llx) to hashtable, offset (%u)",
                                        (long long unsigned)buf->pfn_types[i],
                                        (unsigned) page_offset);
                return -1;
            }
        }

        /* Seek to the starting of the next chunk. */
        temp_offset = prev_offset + pages_this_batch*PAGE_SIZE;
        prev_offset = lseek(fd, temp_offset , SEEK_SET);
        if ( prev_offset < 0 || prev_offset != temp_offset )
        {
            PERROR("ERROR problem while advancing file offset");
            return -errno;
        }

        return count;
    }

    countpages = count;
    for (i = oldcount; i < buf->nr_pages; ++i)
    {
        pagetype = buf->pfn_types[i] & XEN_DOMCTL_PFINFO_LTAB_MASK;
        if ( pagetype == XEN_DOMCTL_PFINFO_XTAB ||
             pagetype == XEN_DOMCTL_PFINFO_BROKEN ||
             pagetype == XEN_DOMCTL_PFINFO_XALLOC )
            --countpages;
    }

    if (!countpages)
        return count;

    /* If Remus Checkpoint Compression is turned on, we will only be
     * receiving the pfn lists now. The compressed pages will come in later,
     * following a <XC_SAVE_ID_COMPRESSED_DATA, compressedChunkSize> tuple.
     */
    if (buf->compressing)
        return pagebuf_get_one(xch, ctx, buf, fd, dom);

    oldcount = buf->nr_physpages;
    buf->nr_physpages += countpages;
    if (!buf->pages) {
        if (!(buf->pages = malloc(buf->nr_physpages * PAGE_SIZE))) {
            ERROR("Could not allocate page buffer");
            return -1;
        }
    } else {
        if (!(ptmp = realloc(buf->pages, buf->nr_physpages * PAGE_SIZE))) {
            ERROR("Could not reallocate page buffer");
            return -1;
        }
        buf->pages = ptmp;
    }
    if ( RDEXACT(fd, buf->pages + oldcount * PAGE_SIZE, countpages * PAGE_SIZE) ) {
        PERROR("Error when reading pages");
        return -1;
    }

    return count;
}

static int pagebuf_get(xc_interface *xch, struct restore_ctx *ctx,
                       pagebuf_t* buf, int fd, uint32_t dom)
{
    int rc;

    buf->nr_physpages = buf->nr_pages = 0;
    buf->compbuf_pos = buf->compbuf_size = 0;

    do {
        rc = pagebuf_get_one(xch, ctx, buf, fd, dom);
    } while (rc > 0);

    if (rc < 0)
        pagebuf_free(buf);

    return rc;
}

static int apply_batch(xc_interface *xch, uint32_t dom, struct restore_ctx *ctx,
                       xen_pfn_t* region_mfn, unsigned long* pfn_type, int pae_extended_cr3,
                       struct xc_mmu* mmu,
                       pagebuf_t* pagebuf, int curbatch)
{
    int i, j, curpage, nr_mfns;
    int k, scount;
    unsigned long superpage_start=INVALID_P2M_ENTRY;
    /* used by debug verify code */
    unsigned long buf[PAGE_SIZE/sizeof(unsigned long)];
    /* Our mapping of the current region (batch) */
    char *region_base;
    /* A temporary mapping, and a copy, of one frame of guest memory. */
    unsigned long *page = NULL;
    int nraces = 0;
    struct domain_info_context *dinfo = &ctx->dinfo;
    int* pfn_err = NULL;
    int rc = -1;

    unsigned long mfn, pfn, pagetype;

    j = pagebuf->nr_pages - curbatch;
    if (j > MAX_BATCH_SIZE)
        j = MAX_BATCH_SIZE;

    /* If we reverted from lazy pager just apply pages */
    if( ctx->pager_fallback )
        goto lazy_pager_fallback;

    /* First pass for this batch: work out how much memory to alloc, and detect superpages */
    nr_mfns = scount = 0;
    for ( i = 0; i < j; i++ )
    {
        unsigned long pfn, pagetype;
        pfn      = pagebuf->pfn_types[i + curbatch] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
        pagetype = pagebuf->pfn_types[i + curbatch] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

        /* For allocation purposes, treat XEN_DOMCTL_PFINFO_XALLOC as a normal page */
        if ( (pagetype != XEN_DOMCTL_PFINFO_XTAB) && 
             (ctx->p2m[pfn] == INVALID_P2M_ENTRY) )
        {
            /* Have a live PFN which hasn't had an MFN allocated */

            /* Logic if we're in the middle of detecting a candidate superpage */
            if ( superpage_start != INVALID_P2M_ENTRY )
            {
                /* Is this the next expected continuation? */
                if ( pfn == superpage_start + scount )
                {
                    if ( !ctx->superpages )
                    {
                        ERROR("Unexpexted codepath with no superpages");
                        return -1;
                    }

                    scount++;

                    /* If we've found a whole superpage, allocate it and update p2m */
                    if ( scount  == SUPERPAGE_NR_PFNS )
                    {
                        unsigned long supermfn;


                        supermfn=superpage_start;
                        if ( xc_domain_populate_physmap_exact(xch, dom, 1,
                                         SUPERPAGE_PFN_SHIFT, 0, &supermfn) != 0 )
                        {
                            DPRINTF("No 2M page available for pfn 0x%lx, fall back to 4K page.\n",
                                    superpage_start);
                            /* If we're falling back from a failed allocation, subtract one
                             * from count, since the last page == pfn, which will behandled
                             * anyway. */
                            scount--;
                            goto fallback;
                        }

                        DPRINTF("Mapping superpage (%d) pfn %lx, mfn %lx\n", scount, superpage_start, supermfn);
                        for (k=0; k<scount; k++)
                        {
                            /* We just allocated a new mfn above; update p2m */
                            ctx->p2m[superpage_start+k] = supermfn+k;
                            ctx->nr_pfns++;
                            /* region_map[] will be set below */
                        }
                        superpage_start=INVALID_P2M_ENTRY;
                        scount=0;
                    }
                    continue;
                }
                
            fallback:
                DPRINTF("Falling back %d pages pfn %lx\n", scount, superpage_start);
                for (k=0; k<scount; k++)
                {
                    ctx->p2m_batch[nr_mfns++] = superpage_start+k; 
                    ctx->p2m[superpage_start+k]--;
                }
                superpage_start = INVALID_P2M_ENTRY;
                scount=0;
            }

            /* Are we ready to start a new superpage candidate? */
            if ( ctx->hvm && ctx->superpages && SUPER_PAGE_START(pfn) )
            {
                superpage_start=pfn;
                scount++;
            }
            else
            {
                /* Add the current pfn to pfn_batch */
                ctx->p2m_batch[nr_mfns++] = pfn;
                ctx->p2m[pfn]--;
            }
        }
    }

    /* Clean up any partial superpage candidates */
    if ( superpage_start != INVALID_P2M_ENTRY )
    {
        DPRINTF("Falling back %d pages pfn %lx\n", scount, superpage_start);
        for (k=0; k<scount; k++)
        {
            ctx->p2m_batch[nr_mfns++] = superpage_start+k; 
            ctx->p2m[superpage_start+k]--;
        }
        superpage_start = INVALID_P2M_ENTRY;
    }

    /* Now allocate a bunch of mfns for this batch */
    if ( nr_mfns )
    {
        DPRINTF("Mapping order 0,  %d; first pfn %lx\n", nr_mfns, ctx->p2m_batch[0]);
    
        if (!ctx->hvm && ctx->superpages)
            rc = alloc_superpage_mfns(xch, dom, ctx, nr_mfns);
        else
            rc = xc_domain_populate_physmap_exact(xch, dom, nr_mfns, 0, 0,
                                                  ctx->p2m_batch);

        if (rc)
        {
            ERROR("Failed to allocate memory for batch.!\n"); 
            errno = ENOMEM;
            return -1;
        }
    }

    if ( ctx->lazy )
    {
        /*
         * If lazy restore we just allocate the pages in the first pass,
         * the loading of actual pages is done by the pager when required.
         */
        rc = nraces ;
        return rc;
    }

  lazy_pager_fallback:
    /* Second pass for this batch: update p2m[] and region_mfn[] */
    nr_mfns = 0; 
    for ( i = 0; i < j; i++ )
    {
        unsigned long pfn, pagetype;
        pfn      = pagebuf->pfn_types[i + curbatch] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
        pagetype = pagebuf->pfn_types[i + curbatch] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

        if ( pagetype != XEN_DOMCTL_PFINFO_XTAB
             && ctx->p2m[pfn] == (INVALID_P2M_ENTRY-1) )
        {
            /* We just allocated a new mfn above; update p2m */
            ctx->p2m[pfn] = ctx->p2m_batch[nr_mfns++]; 
            ctx->nr_pfns++; 
        }

        /* setup region_mfn[] for batch map, if necessary.
         * For HVM guests, this interface takes PFNs, not MFNs */
        if ( pagetype == XEN_DOMCTL_PFINFO_XTAB
             || pagetype == XEN_DOMCTL_PFINFO_XALLOC )
            region_mfn[i] = ~0UL; /* map will fail but we don't care */
        else
            region_mfn[i] = ctx->hvm ? pfn : ctx->p2m[pfn];
    }

    /* Map relevant mfns */
    pfn_err = calloc(j, sizeof(*pfn_err));
    if ( pfn_err == NULL )
    {
        PERROR("allocation for pfn_err failed");
        return -1;
    }
    region_base = xc_map_foreign_bulk(
        xch, dom, PROT_WRITE, region_mfn, pfn_err, j);

    if ( region_base == NULL )
    {
        PERROR("map batch failed");
        free(pfn_err);
        return -1;
    }

    for ( i = 0, curpage = -1; i < j; i++ )
    {
        pfn      = pagebuf->pfn_types[i + curbatch] & ~XEN_DOMCTL_PFINFO_LTAB_MASK;
        pagetype = pagebuf->pfn_types[i + curbatch] &  XEN_DOMCTL_PFINFO_LTAB_MASK;

        if ( pagetype == XEN_DOMCTL_PFINFO_XTAB 
             || pagetype == XEN_DOMCTL_PFINFO_XALLOC)
            /* a bogus/unmapped/allocate-only page: skip it */
            continue;

        if ( pagetype == XEN_DOMCTL_PFINFO_BROKEN )
        {
            if ( xc_set_broken_page_p2m(xch, dom, pfn) )
            {
                ERROR("Set p2m for broken page failed, "
                      "dom=%d, pfn=%lx\n", dom, pfn);
                goto err_mapped;
            }
            continue;
        }

        if (pfn_err[i])
        {
            ERROR("unexpected PFN mapping failure pfn %lx map_mfn %lx p2m_mfn %lx",
                  pfn, region_mfn[i], ctx->p2m[pfn]);
            goto err_mapped;
        }

        ++curpage;

        if ( pfn > dinfo->p2m_size )
        {
            ERROR("pfn out of range");
            goto err_mapped;
        }

        pfn_type[pfn] = pagetype;

        mfn = ctx->p2m[pfn];

        /* In verify mode, we use a copy; otherwise we work in place */
        page = pagebuf->verify ? (void *)buf : (region_base + i*PAGE_SIZE);

        /* Remus - page decompression */
        if (pagebuf->compressing)
        {
            if (xc_compression_uncompress_page(xch, pagebuf->pages,
                                               pagebuf->compbuf_size,
                                               &pagebuf->compbuf_pos,
                                               (char *)page))
            {
                ERROR("Failed to uncompress page (pfn=%lx)\n", pfn);
                goto err_mapped;
            }
        }
        else
            memcpy(page, pagebuf->pages + (curpage + curbatch) * PAGE_SIZE,
                   PAGE_SIZE);

        pagetype &= XEN_DOMCTL_PFINFO_LTABTYPE_MASK;

        if ( (pagetype >= XEN_DOMCTL_PFINFO_L1TAB) &&
             (pagetype <= XEN_DOMCTL_PFINFO_L4TAB) )
        {
            /*
            ** A page table page - need to 'uncanonicalize' it, i.e.
            ** replace all the references to pfns with the corresponding
            ** mfns for the new domain.
            **
            ** On PAE we need to ensure that PGDs are in MFNs < 4G, and
            ** so we may need to update the p2m after the main loop.
            ** Hence we defer canonicalization of L1s until then.
            */
            if ((ctx->pt_levels != 3) ||
                pae_extended_cr3 ||
                (pagetype != XEN_DOMCTL_PFINFO_L1TAB)) {

                if (!uncanonicalize_pagetable(xch, dom, ctx, page)) {
                    /*
                    ** Failing to uncanonicalize a page table can be ok
                    ** under live migration since the pages type may have
                    ** changed by now (and we'll get an update later).
                    */
                    DPRINTF("PT L%ld race on pfn=%08lx mfn=%08lx\n",
                            pagetype >> 28, pfn, mfn);
                    nraces++;
                    continue;
                }
            }
        }
        else if ( pagetype != XEN_DOMCTL_PFINFO_NOTAB )
        {
            ERROR("Bogus page type %lx page table is out of range: "
                  "i=%d p2m_size=%lu", pagetype, i, dinfo->p2m_size);
            goto err_mapped;
        }

        if ( pagebuf->verify )
        {
            int res = memcmp(buf, (region_base + i*PAGE_SIZE), PAGE_SIZE);
            if ( res )
            {
                int v;

                DPRINTF("************** pfn=%lx type=%lx gotcs=%08lx "
                        "actualcs=%08lx\n", pfn, pagebuf->pfn_types[pfn],
                        csum_page(region_base + (i + curbatch)*PAGE_SIZE),
                        csum_page(buf));

                for ( v = 0; v < 4; v++ )
                {
                    unsigned long *p = (unsigned long *)
                        (region_base + i*PAGE_SIZE);
                    if ( buf[v] != p[v] )
                        DPRINTF("    %d: %08lx %08lx\n", v, buf[v], p[v]);
                }
            }
        }

        if ( !ctx->hvm &&
             xc_add_mmu_update(xch, mmu,
                               (((unsigned long long)mfn) << PAGE_SHIFT)
                               | MMU_MACHPHYS_UPDATE, pfn) )
        {
            PERROR("failed machpys update mfn=%lx pfn=%lx", mfn, pfn);
            goto err_mapped;
        }
    } /* end of 'batch' for loop */

    rc = nraces;

  err_mapped:
    munmap(region_base, j*PAGE_SIZE);
    free(pfn_err);

    return rc;
}

/* Get mem event requests from shared ring. */
static void get_request(struct mem_event *mem_event, mem_event_request_t *req)
{
    mem_event_back_ring_t *back_ring;
    RING_IDX req_cons;

    back_ring = &mem_event->back_ring;
    req_cons = back_ring->req_cons;

    /* Copy request */
    memcpy(req, RING_GET_REQUEST(back_ring, req_cons), sizeof(*req));
    req_cons++;

    /* Update ring */
    back_ring->req_cons = req_cons;
    back_ring->sring->req_event = req_cons + 1;
}

/* Put mem event response onto shared ring. */
static void put_response(struct mem_event *mem_event, mem_event_response_t *rsp)
{
    mem_event_back_ring_t *back_ring;
    RING_IDX rsp_prod;

    back_ring = &mem_event->back_ring;
    rsp_prod = back_ring->rsp_prod_pvt;

    /* Copy response */
    memcpy(RING_GET_RESPONSE(back_ring, rsp_prod), rsp, sizeof(*rsp));
    rsp_prod++;

    /* Update ring */
    back_ring->rsp_prod_pvt = rsp_prod;
    RING_PUSH_RESPONSES(back_ring);
}

/* Read the page requested by pager and add the page to guest memory. */
static int populate_page(xc_interface *xch,
                         struct mem_event *mem_event,
                         void *pager_buffer, unsigned long pfn,
                         off_t off, int fd)
{
    int rc;
    unsigned char oom = 0;
    int read_bytes = 0;
    int bytes;
    off_t offset;

    DPRINTF("populate_page < pfn %lx pageslot %d\n", pfn, (int) off);

    /* Read page from saved image. */
    offset = lseek(fd, off, SEEK_SET);
    if ( offset < 0 || offset != off )
    {
        PERROR("Error seeking to starting of page.");
        return -errno;
    }

    while ( read_bytes < PAGE_SIZE )
    {
        bytes = read(fd, pager_buffer + read_bytes, PAGE_SIZE - read_bytes);
        if ( bytes <= 0 )
        {
            PERROR("Error seeking to starting of page.");
            return -errno;
        }
        read_bytes += bytes;
    }

    do
    {
        /* Tell Xen to allocate a page for the domain */
        rc = xc_mem_paging_load(xch, mem_event->domain_id, pfn, pager_buffer);
        if ( rc < 0 )
        {
            if ( errno == ENOMEM )
            {
                /*
                 * This is actually a temporary solution until we find a more
                 * complete and reliable solution.
                 */
                if ( oom++ == 0 )
                    DPRINTF("ENOMEM while preparing pfn %lx\n", pfn);
                sleep(1);
                continue;
            }
            PERROR("Error loading %lx during page-in", pfn);
            rc = -errno;
            break;
        }
    }
    while (rc);

    return rc;
}

#define PAGER_EVENT_RECEIVED        0
#define PAGER_EVENT_TIMEOUT         1

/*
 * waits for an event from xen or timeout.
 * Return semantics are -
 * -errno for error.
 * 0 for successful event.
 * 1 for timeout.
 * 2 for domain shutdown.
 */
static int wait_for_event_or_timeout(xc_interface *xch,
                                     struct restore_ctx *ctx,
                                     struct mem_event *mem_event)
{
    xc_evtchn *xce = mem_event->xce_handle;
    struct pollfd fd;
    int port;
    int rc;
    int timeout = 0;

    /* Wait for event channel and xenstore */
    fd.fd = xc_evtchn_fd(xce);
    fd.events = POLLIN | POLLERR;

    rc = poll(&fd, 1, timeout);
    if ( rc < 0 )
    {
        if (errno == EINTR)
            return PAGER_EVENT_TIMEOUT;

        PERROR("Poll exited with an error");
        return -errno;
    }

    if ( rc && fd.revents & POLLIN )
    {
        DPRINTF("Got event from evtchn\n");
        port = xc_evtchn_pending(xce);
        if ( port == -1 )
        {
            PERROR("Failed to read port from event channel");
            rc = -errno;
            goto err;
        }
        if ( port != mem_event->port )
        {
            PERROR("Event chanel port value mismatch");
            rc = -errno;
            goto err;
        }

        rc = xc_evtchn_unmask(xce, port);
        if ( rc < 0 )
        {
            PERROR("Failed to unmask event channel port");
            rc = -errno;
            goto err;
        }

        rc = PAGER_EVENT_RECEIVED;
    }
    else
        rc = PAGER_EVENT_TIMEOUT;

    err:
        return rc;
}

/*
 * Setup the lazy restore pager to serve the pagein requests by opening
 * connection to xenstore enabling mempaging, setting up a ring to
 * communicate with xen for mem requests.
 * The pager continuously looks for incoming paging requests and populates
 * required pages to the guest memory by reading them from the save image.
 * The pager writes its pid to xenstore at the path
 *  /local/domain/0/restore-pager/$domain_id/pid -> $pid
 * Returns -
 * 0 on successful completion.
 * 1 on setup failure.
 * -errno on error after successful setup.
 */
static int lazy_restore_pager(xc_interface *xch, struct restore_ctx *ctx,
                              pagebuf_t* buf, tailbuf_t *tailbuf, int fd,
                              domid_t dom, int pipe_fd)
{
    int rc = -1, rc2;
    off_t *off;
    uint32_t max_pages;
    unsigned long *bitmap = NULL;
    void *pager_buffer = NULL;
    struct mem_event _mem_event;
    struct mem_event *mem_event = &_mem_event;
    mem_event_request_t req;
    mem_event_response_t rsp;
    xc_domaininfo_t domain_info;
    bool enabled_paging = false;

    memset(mem_event, 0, sizeof(*mem_event));
    mem_event->domain_id = dom;

    DPRINTF("restore-pager: Inside lazy restore pager pid - %u",(unsigned)getpid());

    /* Open event channel */
    mem_event->xce_handle = xc_evtchn_open(NULL, 0);
    if ( mem_event->xce_handle == NULL )
    {
        PERROR("restore-pager: Failed to open event channel");
        goto out;
    }

    DPRINTF("restore-pager: Opened up xce event channel");

    /* Allocate the paging buffer. */
    errno = posix_memalign(&pager_buffer, PAGE_SIZE, PAGE_SIZE);
    if ( errno != 0 )
    {
        PERROR("restore-pager: Error while aligning paging buffer to PAGE_SIZE");
        goto out;
    }

    /* Lock buffer in memory so it can't be paged out */
    if ( mlock(pager_buffer, PAGE_SIZE) < 0 )
    {
        PERROR("restore-pager: error locking paging buffer into memory.");
        goto out;
    }
    DPRINTF("restore-pager: mem aligned and memlocked pager buffers");

    /* Get max_pages from guest */
    rc = xc_domain_getinfolist(xch, mem_event->domain_id, 1,
                               &domain_info);
    if ( rc != 1 )
    {
        PERROR("restore-pager: Error getting domain info");
        rc = -1;
        goto out;
    }
    max_pages = domain_info.max_pages;

    DPRINTF("restore-pager: Got max pages from xen %u",max_pages);

    /* Allocate bitmap for tracking pages that have been paged in */
    bitmap = bitmap_alloc(max_pages);
    if ( !bitmap )
    {
        PERROR("restore-pager: Error allocating bitmap");
        rc = -1;
        goto out;
    }
    DPRINTF("restore-pager: max_pages = %d\n", max_pages);

    /* Initialize paging by setting up ring and event channel. */
    rc = xc_mem_paging_ring_setup(xch, mem_event->xce_handle,
                                  mem_event->domain_id,
                                  mem_event->ring_page,
                                  &mem_event->port,
                                  &mem_event->evtchn_port,
                                  &mem_event->back_ring);
    if( rc < 0 )
    {
        PERROR("Could not initialize mem paging");
        goto out;
    }
    DPRINTF("restore-pager: ring and event channel setup successful");
    enabled_paging = true;

    rc = nominate_and_evict(xch, ctx, buf, tailbuf, dom);
    if ( rc < 0 )
    {
        PERROR("Error while nominating and evicting pfn's");
        goto out;
    }

    /* Wakeup the parent process and close the pipe afterwards. */
    rc = write(pipe_fd, LAZY_RESTORE_PAGER_SUCCESS,
               strlen(LAZY_RESTORE_PAGER_FAILURE));
    if( rc < 0 )
    {
        PERROR("Error while writing success status to pipe");
        goto out;
    }
    rc = close(pipe_fd);
    if( rc < 0 )
        PERROR("Error closing pager end of pipe");

    /* Start looping to check for incoming page-in requests. */
    for ( ; ; )
    {
        if( hashtable_count(buf->pfn_to_fileoffset) == 0 )
        {
            DPRINTF("Hashtable count dropped to zero.");
            rc = 0;
            goto out;
        }

        rc = wait_for_event_or_timeout(xch, ctx, mem_event);
        if( rc < 0 )
        {
            PERROR("Problem waiting for event");
            goto out;
        }
        else if ( rc == PAGER_EVENT_TIMEOUT )
        {
            DPRINTF("Event poll timeout, policy not implemented");
        }

        while ( RING_HAS_UNCONSUMED_REQUESTS(&mem_event->back_ring) )
        {
            rc = -1;
            get_request(mem_event, &req);

            /* Check if the page has already been paged in */
            if ( test_bit(req.gfn, bitmap) )
            {
                /* Find where in the paging file to read from */
                off = hashtable_search_pfn( buf->pfn_to_fileoffset, &req.gfn );
                if( off == NULL )
                {
                    PERROR("Error page %"PRIx64" not found", req.gfn);
                    goto out;
                }

                if ( req.flags & MEM_EVENT_FLAG_DROP_PAGE )
                {
                    DPRINTF("drop_page ^ gfn %"PRIx64"", req.gfn);
                }
                else
                {
                    /* Populate the page */
                    rc = populate_page(xch, mem_event, pager_buffer,
                                       req.gfn, *off, fd);
                    if ( rc < 0 )
                    {
                        ERROR("Error populating page %"PRIx64"", req.gfn);
                        goto out;
                    }
                }
                /* Clear the bit for both dropped pages and populated pages */
                clear_bit(req.gfn, bitmap);

                /* Remove the entry from hashtable. */
                off = hashtable_remove_pfn( buf->pfn_to_fileoffset, &req.gfn );
                if( off == NULL )
                {
                    PERROR("Error removing page %"PRIx64" from hashtable",
                                                                 req.gfn);
                    goto out;
                }
                free(off);

                /* Prepare the response */
                rsp.gfn = req.gfn;
                rsp.vcpu_id = req.vcpu_id;
                rsp.flags = req.flags;

                /* Put the page info on the ring */
                put_response(mem_event, &rsp);
                rc = xc_evtchn_notify(mem_event->xce_handle,
                                      mem_event->port);
                if ( rc < 0 )
                {
                    PERROR("Error notifying event for page %"PRIx64"", req.gfn);
                    goto out;
                }
            }
            else
            {
                /* Search for pfn to look for potential duplicates. */
                off = hashtable_search_pfn( buf->pfn_to_fileoffset, &req.gfn );
                if( off != NULL )
                {
                    PERROR("Error duplicate page %"PRIx64" found in hashtable",
                                                                      req.gfn);
                    goto out;
                }

                DPRINTF("page %s populated (domain = %d; vcpu = %d;"
                        " gfn = %"PRIx64"; paused = %d; evict_fail = %d)",
                        req.flags & MEM_EVENT_FLAG_EVICT_FAIL ? "not" : "already",
                        mem_event->domain_id, req.vcpu_id, req.gfn,
                        !!(req.flags & MEM_EVENT_FLAG_VCPU_PAUSED) ,
                        !!(req.flags & MEM_EVENT_FLAG_EVICT_FAIL) );

                /* Tell Xen to resume the vcpu */
                if (( req.flags & MEM_EVENT_FLAG_VCPU_PAUSED ) ||
                    ( req.flags & MEM_EVENT_FLAG_EVICT_FAIL  ))
                {
                    /* Prepare the response */
                    rsp.gfn = req.gfn;
                    rsp.vcpu_id = req.vcpu_id;
                    rsp.flags = req.flags;

                    /* Put the page info on the ring */
                    put_response(mem_event, &rsp);
                    rc = xc_evtchn_notify(mem_event->xce_handle,
                                          mem_event->port);
                    if ( rc < 0 )
                    {
                        PERROR("Error resuming page %"PRIx64"", req.gfn);
                        goto out;
                    }
                }
            }
        }
    }

  out:
    if( mem_event )
    {
        if( enabled_paging )
        {
            /* Tear down domain paging and ring setup in Xen */
            rc2 = xc_mem_paging_ring_teardown(xch, mem_event->xce_handle,
                                             mem_event->domain_id,
                                             mem_event->ring_page,
                                             &mem_event->port);
            if ( rc2 < 0 )
                PERROR("Error in mem paging teardown");
            else
                DPRINTF("tear down ring and mempaging successful");
        }
        if( mem_event->xce_handle )
        {
            /* Close event channel */
            rc2 = xc_evtchn_close(mem_event->xce_handle);
            if ( rc2 != 0 )
                PERROR("Error closing event channel");
        }
    }
    if( pager_buffer )
    {
        /* unlock buffer from memory */
        if ( munlock(pager_buffer, PAGE_SIZE) < 0 )
            PERROR("error locking paging buffer into memory.");
    }
    if ( !enabled_paging ) /* Error received during setup */
        rc = 1;

    free(bitmap);
    free(pager_buffer);

    if ( rc < 0 )
        rc = -errno;

    return rc;
}

/* Start the lazy restore pager daemon */
static void lazy_restore_pager_daemon(xc_interface *xch,
                                     struct restore_ctx *ctx,
                                     pagebuf_t* buf, tailbuf_t *tailbuf,
                                     int io_fd, domid_t dom, int *pipe_c2p)
{
    int rc, i;
    pid_t sid;
    FILE *log_file = NULL;
    char log_path[80];
    xentoollog_logger *dbg = NULL;
    bool wakeup_parent = true;

    /* Pager needs to send message to parent so close read end. */
    close(pipe_c2p[0]);

    /* Change the working directory to root. */
    if( chdir("/") < 0 )
    {
        PERROR("restore pager: chdir failed");
    }

    /* Create a new session id*/
    sid = setsid();
    if( sid == (pid_t)-1 )
    {
        PERROR("restore pager: setsid failed");
    }

    /* Set the umask to 077, so that no one can read/write our data.*/
    umask(077);

    sprintf(log_path, XC_LAZY_RESTORE_PAGER_LOG_FILE, dom);
    DPRINTF("restore-pager: logging to log file %s\n",log_path);

    /* Close connection to Xen so that we can open new log */
    rc = xc_interface_close(xch);
    if ( rc != 0 )
    {
        ERROR("Error closing connection to xen");
        xch = NULL;
        goto err;
    }

    /* Close the unnecessary file descriptors. */
    for ( i=0; i<1024; i++ )
    {
        if( i == io_fd || i == pipe_c2p[1] )
            continue;
        close(i);
    }

    log_file = fopen(log_path, "w");
    if ( !log_file )
    {
        ERROR("restore pager: error opening log file");
        goto err;
    }
    dbg = (xentoollog_logger *)xtl_createlogger_stdiostream(log_file, XTL_DEBUG, 0);

    /* Open connection to xen */
    xch = xc_interface_open(dbg, NULL, 0);
    if ( !xch )
    {
        ERROR("restore pager: error opening connection to xen");
        goto err;
    }

    DPRINTF("Opened up connection to xen with new log.\n");

    /* start lazy restore pager */
    rc = lazy_restore_pager(xch, ctx, buf, tailbuf,
                            io_fd, dom, pipe_c2p[1]);
    if ( rc == 1 )
    {
        PERROR("restore-pager: Error during lazy restore pager setup");
        goto err;
    }

    DPRINTF("restore-pager: pager exit of domid %u with rc=%d", dom, rc);
    wakeup_parent = false; /*Success, We don't need to wakeup parent */

  err:
    if ( wakeup_parent )
    {
        rc = write(pipe_c2p[1], LAZY_RESTORE_PAGER_FAILURE,
                    strlen(LAZY_RESTORE_PAGER_FAILURE));
        if( rc < 0 )
            ERROR("restore-pager: Error while writing setup failed status to pipe");
        rc = close(pipe_c2p[1]);
        if( rc < 0 )
            ERROR("restore-pager: Error closing pager end of pipe");
        rc = 1;
        goto out;
    }
    if ( xch )
    {
        /* Close connection to Xen. */
        rc = xc_interface_close(xch);
        if ( rc != 0 )
        {
            ERROR("restore-pager: Error closing connection to xen");
            rc = 1;
        }
    }
    if ( log_file )
        rc = fclose(log_file);

    rc = 0;

  out:
    exit(rc);
}

int xc_domain_restore(xc_interface *xch, int io_fd, uint32_t dom,
                      unsigned int store_evtchn, unsigned long *store_mfn,
                      domid_t store_domid, unsigned int console_evtchn,
                      unsigned long *console_mfn, domid_t console_domid,
                      unsigned int hvm, unsigned int pae, int superpages,
                      int checkpointed_stream, int lazy,
                      struct restore_callbacks *callbacks)
{
    DECLARE_DOMCTL;
    xc_dominfo_t info;
    int rc = 1, frc, i, j, n, m, pae_extended_cr3 = 0, ext_vcpucontext = 0;
    uint32_t vcpuextstate_size = 0;
    unsigned long mfn, pfn;
    int nraces = 0;
    off_t saved_offset = 0;

    /* The new domain's shared-info frame number. */
    unsigned long shared_info_frame;
    unsigned char shared_info_page[PAGE_SIZE]; /* saved contents from file */
    shared_info_any_t *old_shared_info = 
        (shared_info_any_t *)shared_info_page;
    shared_info_any_t *new_shared_info;

    /* A copy of the CPU context of the guest. */
    DECLARE_HYPERCALL_BUFFER(vcpu_guest_context_any_t, ctxt);

    /* A copy of the CPU eXtended States of the guest. */
    DECLARE_HYPERCALL_BUFFER(void, buffer);

    /* A table containing the type of each PFN (/not/ MFN!). */
    unsigned long *pfn_type = NULL;

    /* A table of MFNs to map in the current region */
    xen_pfn_t *region_mfn = NULL;

    /* A copy of the pfn-to-mfn table frame list. */
    xen_pfn_t *p2m_frame_list = NULL;
    
    /* A temporary mapping of the guest's start_info page. */
    start_info_any_t *start_info;

    /* Our mapping of the current region (batch) */
    char *region_base;

    struct xc_mmu *mmu = NULL;

    struct mmuext_op pin[MAX_PIN_BATCH];
    unsigned int nr_pins;

    uint64_t vcpumap[XC_SR_MAX_VCPUS/64] = { 1ULL };
    unsigned int max_vcpu_id = 0;
    int new_ctxt_format = 0;

    pagebuf_t pagebuf;
    tailbuf_t tailbuf, tmptail;
    struct toolstack_data_t tdata, tdatatmp;
    void* vcpup;
    uint64_t console_pfn = 0;

    int orig_io_fd_flags;

    struct restore_ctx _ctx;
    struct restore_ctx *ctx = &_ctx;
    struct domain_info_context *dinfo = &ctx->dinfo;

    DPRINTF("%s: starting restore of new domid %u", __func__, dom);

    pagebuf_init(&pagebuf);
    memset(&tailbuf, 0, sizeof(tailbuf));
    tailbuf.ishvm = hvm;
    memset(&tdata, 0, sizeof(tdata));

    memset(ctx, 0, sizeof(*ctx));

    ctx->superpages = superpages;
    ctx->hvm = hvm;
    ctx->last_checkpoint = !checkpointed_stream;
    ctx->lazy = lazy;

    ctxt = xc_hypercall_buffer_alloc(xch, ctxt, sizeof(*ctxt));

    if ( ctxt == NULL )
    {
        PERROR("Unable to allocate VCPU ctxt buffer");
        return 1;
    }

    if ( (orig_io_fd_flags = fcntl(io_fd, F_GETFL, 0)) < 0 ) {
        PERROR("unable to read IO FD flags");
        goto out;
    }

    if ( RDEXACT(io_fd, &dinfo->p2m_size, sizeof(unsigned long)) )
    {
        PERROR("read: p2m_size");
        goto out;
    }
    DPRINTF("%s: p2m_size = %lx\n", __func__, dinfo->p2m_size);

    if ( !get_platform_info(xch, dom,
                            &ctx->max_mfn, &ctx->hvirt_start, &ctx->pt_levels, &dinfo->guest_width) )
    {
        ERROR("Unable to get platform info.");
        return 1;
    }
    
    /* The *current* word size of the guest isn't very interesting; for now
     * assume the guest will be the same as we are.  We'll fix that later
     * if we discover otherwise. */
    dinfo->guest_width = sizeof(unsigned long);
    ctx->pt_levels = (dinfo->guest_width == 8) ? 4 : 3;
    
    if ( !hvm ) 
    {
        /* Load the p2m frame list, plus potential extended info chunk */
        p2m_frame_list = load_p2m_frame_list(xch, ctx,
            io_fd, &pae_extended_cr3, &ext_vcpucontext,
            &vcpuextstate_size);

        if ( !p2m_frame_list )
            goto out;

        /* Now that we know the word size, tell Xen about it */
        memset(&domctl, 0, sizeof(domctl));
        domctl.domain = dom;
        domctl.cmd    = XEN_DOMCTL_set_address_size;
        domctl.u.address_size.size = dinfo->guest_width * 8;
        frc = do_domctl(xch, &domctl);
        if ( frc != 0 )
        {
            PERROR("Unable to set guest address size.");
            goto out;
        }
    }

    /* We want zeroed memory so use calloc rather than malloc. */
    ctx->p2m   = calloc(dinfo->p2m_size, sizeof(xen_pfn_t));
    pfn_type   = calloc(dinfo->p2m_size, sizeof(unsigned long));

    region_mfn = malloc(ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT));
    ctx->p2m_batch = malloc(ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT));
    if (!ctx->hvm && ctx->superpages)
    {
        ctx->p2m_saved_batch =
            malloc(ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT));
        if ( ctx->p2m_saved_batch == NULL )
        {
            ERROR("saved batch memory alloc failed");
            errno = ENOMEM;
            goto out;
        }
    }

    if ( (ctx->p2m == NULL) || (pfn_type == NULL) ||
         (region_mfn == NULL) || (ctx->p2m_batch == NULL) )
    {
        ERROR("memory alloc failed");
        errno = ENOMEM;
        goto out;
    }

    memset(region_mfn, 0,
           ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT)); 
    memset(ctx->p2m_batch, 0,
           ROUNDUP(MAX_BATCH_SIZE * sizeof(xen_pfn_t), PAGE_SHIFT)); 

    /* Get the domain's shared-info frame. */
    if ( xc_domain_getinfo(xch, (domid_t)dom, 1, &info) != 1 )
    {
        PERROR("Could not get information on new domain");
        goto out;
    }
    shared_info_frame = info.shared_info_frame;

    /* Mark all PFNs as invalid; we allocate on demand */
    for ( pfn = 0; pfn < dinfo->p2m_size; pfn++ )
        ctx->p2m[pfn] = INVALID_P2M_ENTRY;

    mmu = xc_alloc_mmu_updates(xch, dom);
    if ( mmu == NULL )
    {
        PERROR("Could not initialise for MMU updates");
        goto out;
    }

    if ( ctx->lazy )
    {
        DPRINTF("lazy switch enabled for restore\n");
        if ( !hvm )
        {
            DPRINTF("lazy restore should be called only for HVM guests\n"
                    "reverting to non lazy restore");
            ctx->lazy = 0;
            goto loadpages;
        }

        saved_offset = lseek(io_fd, 0, SEEK_CUR);
        if ( saved_offset < 0 )
        {
            PERROR("ERROR problem saving file offset");
            ctx->lazy = 0;
            goto loadpages;
        }

        pagebuf.pfn_to_fileoffset = create_hashtable(16, hash_from_key_fn,
                                                     keys_equal_fn);
        if ( !pagebuf.pfn_to_fileoffset )
        {
            PERROR("ERROR problem creating hashtable for lazy restore.");
            ctx->lazy = 0;
        }
    }

 loadpages:
    if ( !ctx->lazy )
        xc_report_progress_start(xch, "Reloading memory pages",
                                 dinfo->p2m_size);
    else
        xc_report_progress_start(xch, "Reading page offsets form file",
                                 dinfo->p2m_size);
    /*
     * Now simply read each saved frame into its new machine frame.
     * We uncanonicalise page tables as we go.
     */

    n = m = 0;
    for ( ; ; )
    {
        int j, curbatch;
        xc_report_progress_step(xch, n, dinfo->p2m_size);

        if ( !ctx->completed ) {
            pagebuf.nr_physpages = pagebuf.nr_pages = 0;
            pagebuf.compbuf_pos = pagebuf.compbuf_size = 0;
            if ( pagebuf_get_one(xch, ctx, &pagebuf, io_fd, dom) < 0 ) {
                PERROR("Error when reading batch");
                goto out;
            }
        }
        j = pagebuf.nr_pages;
        pagebuf.total_pages += j;

        /* Meaningful only for non lazy restore. */
        if ( !ctx->lazy && !ctx->pager_fallback )
            DBGPRINTF("batch %d\n",j);

        if ( j == 0 ) {
            /* catch vcpu updates */
            if (pagebuf.new_ctxt_format) {
                max_vcpu_id = pagebuf.max_vcpu_id;
                memcpy(vcpumap, pagebuf.vcpumap, vcpumap_sz(max_vcpu_id));
            }
            /* should this be deferred? does it change? */
            if ( pagebuf.identpt )
                xc_hvm_param_set(xch, dom, HVM_PARAM_IDENT_PT, pagebuf.identpt);
            if ( pagebuf.paging_ring_pfn )
                xc_hvm_param_set(xch, dom, HVM_PARAM_PAGING_RING_PFN, pagebuf.paging_ring_pfn);
            if ( pagebuf.access_ring_pfn )
                xc_hvm_param_set(xch, dom, HVM_PARAM_ACCESS_RING_PFN, pagebuf.access_ring_pfn);
            if ( pagebuf.sharing_ring_pfn )
                xc_hvm_param_set(xch, dom, HVM_PARAM_SHARING_RING_PFN, pagebuf.sharing_ring_pfn);
            if ( pagebuf.vm86_tss )
                xc_hvm_param_set(xch, dom, HVM_PARAM_VM86_TSS, pagebuf.vm86_tss);
            if ( pagebuf.console_pfn )
                console_pfn = pagebuf.console_pfn;
            if ( pagebuf.vm_generationid_addr )
                xc_hvm_param_set(xch, dom, HVM_PARAM_VM_GENERATION_ID_ADDR,
                                 pagebuf.vm_generationid_addr);

            break;  /* our work here is done */
        }

        /* break pagebuf into batches */
        curbatch = 0;
        while ( curbatch < j ) {
            int brc;

            brc = apply_batch(xch, dom, ctx, region_mfn, pfn_type,
                              pae_extended_cr3, mmu, &pagebuf, curbatch);
            if ( brc < 0 )
                goto out;

            nraces += brc;

            curbatch += MAX_BATCH_SIZE;
        }

        pagebuf.nr_physpages = pagebuf.nr_pages = 0;
        pagebuf.compbuf_pos = pagebuf.compbuf_size = 0;

        n += j; /* crude stats */

        /* 
         * Discard cache for portion of file read so far up to last
         *  page boundary every 16MB or so.
         */
        m += j;
        if ( m > MAX_PAGECACHE_USAGE )
        {
            discard_file_cache(xch, io_fd, 0 /* no flush */);
            m = 0;
        }
    }

    /*
     * Ensure we flush all machphys updates before potential PAE-specific
     * reallocations below.
     */
    if ( !hvm && xc_flush_mmu_updates(xch, mmu) )
    {
        PERROR("Error doing flush_mmu_updates()");
        goto out;
    }

    // DPRINTF("Received all pages (%d races)\n", nraces);

    if ( !ctx->completed ) {

        if ( buffer_tail(xch, ctx, &tailbuf, io_fd, max_vcpu_id, vcpumap,
                         ext_vcpucontext, vcpuextstate_size) < 0 ) {
            ERROR ("error buffering image tail");
            goto out;
        }

        ctx->completed = 1;

        /*
         * If more checkpoints are expected then shift into
         * nonblocking mode for the remainder.
         */
        if ( !ctx->last_checkpoint )
            fcntl(io_fd, F_SETFL, orig_io_fd_flags | O_NONBLOCK);

        /*
         * If sender had sent enable compression flag, switch to compressed
         * checkpoints mode once the first checkpoint is received.
         */
        if (ctx->compressing)
            pagebuf.compressing = 1;
    }

    if (pagebuf.viridian != 0)
        xc_hvm_param_set(xch, dom, HVM_PARAM_VIRIDIAN, 1);

    /*
     * If we are migrating in from a host that does not support
     * secondary emulators then nr_ioreq_server_pages will be 0, since
     * there will be no XC_SAVE_ID_HVM_NR_IOREQ_SERVER_PAGES chunk in
     * the image.
     * If we are migrating from a host that does support secondary
     * emulators then the XC_SAVE_ID_HVM_NR_IOREQ_SERVER_PAGES chunk
     * will exist and is guaranteed to have a non-zero value. The
     * existence of that chunk also implies the existence of the
     * XC_SAVE_ID_HVM_IOREQ_SERVER_PFN chunk, which is also guaranteed
     * to have a non-zero value.
     */
    if (!pagebuf.nr_ioreq_server_pages ^ !pagebuf.ioreq_server_pfn) {
        ERROR("Inconsistent IOREQ Server settings (nr=%"PRIx64", pfn=%"PRIx64")",
              pagebuf.nr_ioreq_server_pages, pagebuf.ioreq_server_pfn);
    } else {
        if (pagebuf.nr_ioreq_server_pages != 0 &&
            pagebuf.ioreq_server_pfn != 0) {
            xc_hvm_param_set(xch, dom, HVM_PARAM_NR_IOREQ_SERVER_PAGES,
                             pagebuf.nr_ioreq_server_pages);
            xc_hvm_param_set(xch, dom, HVM_PARAM_IOREQ_SERVER_PFN,
                             pagebuf.ioreq_server_pfn);
        }
    }

    if (pagebuf.acpi_ioport_location == 1) {
        DBGPRINTF("Use new firmware ioport from the checkpoint\n");
        xc_hvm_param_set(xch, dom, HVM_PARAM_ACPI_IOPORTS_LOCATION, 1);
    } else if (pagebuf.acpi_ioport_location == 0) {
        DBGPRINTF("Use old firmware ioport from the checkpoint\n");
    } else {
        ERROR("Error, unknow acpi ioport location (%"PRId64")", pagebuf.acpi_ioport_location);
    }

    tdatatmp = tdata;
    tdata = pagebuf.tdata;
    pagebuf.tdata = tdatatmp;

    if ( ctx->last_checkpoint )
    {
        // DPRINTF("Last checkpoint, finishing\n");
        goto finish;
    }

    // DPRINTF("Buffered checkpoint\n");

    if ( pagebuf_get(xch, ctx, &pagebuf, io_fd, dom) ) {
        PERROR("error when buffering batch, finishing");
        goto out;
    }
    memset(&tmptail, 0, sizeof(tmptail));
    tmptail.ishvm = hvm;
    if ( buffer_tail(xch, ctx, &tmptail, io_fd, max_vcpu_id, vcpumap,
                     ext_vcpucontext, vcpuextstate_size) < 0 ) {
        ERROR ("error buffering image tail, finishing");
        goto out;
    }
    tailbuf_free(&tailbuf);
    memcpy(&tailbuf, &tmptail, sizeof(tailbuf));

    goto loadpages;

  finish:
    if ( hvm )
        goto finish_hvm;

    if ( (ctx->pt_levels == 3) && !pae_extended_cr3 )
    {
        /*
        ** XXX SMH on PAE we need to ensure PGDs are in MFNs < 4G. This
        ** is a little awkward and involves (a) finding all such PGDs and
        ** replacing them with 'lowmem' versions; (b) upating the p2m[]
        ** with the new info; and (c) canonicalizing all the L1s using the
        ** (potentially updated) p2m[].
        **
        ** This is relatively slow (and currently involves two passes through
        ** the pfn_type[] array), but at least seems to be correct. May wish
        ** to consider more complex approaches to optimize this later.
        */

        int j, k;
        
        /* First pass: find all L3TABs current in > 4G mfns and get new mfns */
        for ( i = 0; i < dinfo->p2m_size; i++ )
        {
            if ( ((pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) ==
                  XEN_DOMCTL_PFINFO_L3TAB) &&
                 (ctx->p2m[i] > 0xfffffUL) )
            {
                unsigned long new_mfn;
                uint64_t l3ptes[4];
                uint64_t *l3tab;

                l3tab = (uint64_t *)
                    xc_map_foreign_range(xch, dom, PAGE_SIZE,
                                         PROT_READ, ctx->p2m[i]);
                if ( l3tab == NULL )
                {
                    PERROR("xc_map_foreign_range failed (for l3tab)");
                    goto out;
                }

                for ( j = 0; j < 4; j++ )
                    l3ptes[j] = l3tab[j];

                munmap(l3tab, PAGE_SIZE);

                new_mfn = xc_make_page_below_4G(xch, dom, ctx->p2m[i]);
                if ( !new_mfn )
                {
                    PERROR("Couldn't get a page below 4GB :-(");
                    goto out;
                }

                ctx->p2m[i] = new_mfn;
                if ( xc_add_mmu_update(xch, mmu,
                                       (((unsigned long long)new_mfn)
                                        << PAGE_SHIFT) |
                                       MMU_MACHPHYS_UPDATE, i) )
                {
                    PERROR("Couldn't m2p on PAE root pgdir");
                    goto out;
                }

                l3tab = (uint64_t *)
                    xc_map_foreign_range(xch, dom, PAGE_SIZE,
                                         PROT_READ | PROT_WRITE, ctx->p2m[i]);
                if ( l3tab == NULL )
                {
                    PERROR("xc_map_foreign_range failed (for l3tab, 2nd)");
                    goto out;
                }

                for ( j = 0; j < 4; j++ )
                    l3tab[j] = l3ptes[j];

                munmap(l3tab, PAGE_SIZE);
            }
        }

        /* Second pass: find all L1TABs and uncanonicalize them */
        j = 0;

        for ( i = 0; i < dinfo->p2m_size; i++ )
        {
            if ( ((pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) ==
                  XEN_DOMCTL_PFINFO_L1TAB) )
            {
                region_mfn[j] = ctx->p2m[i];
                j++;
            }

            if ( (i == (dinfo->p2m_size-1)) || (j == MAX_BATCH_SIZE) )
            {
                region_base = xc_map_foreign_pages(
                    xch, dom, PROT_READ | PROT_WRITE, region_mfn, j);
                if ( region_base == NULL )
                {
                    PERROR("map batch failed");
                    goto out;
                }

                for ( k = 0; k < j; k++ )
                {
                    if ( !uncanonicalize_pagetable(
                        xch, dom, ctx,
                        region_base + k*PAGE_SIZE) )
                    {
                        ERROR("failed uncanonicalize pt!");
                        goto out;
                    }
                }

                munmap(region_base, j*PAGE_SIZE);
                j = 0;
            }
        }

        if ( xc_flush_mmu_updates(xch, mmu) )
        {
            PERROR("Error doing xc_flush_mmu_updates()");
            goto out;
        }
    }

    /*
     * Pin page tables. Do this after writing to them as otherwise Xen
     * will barf when doing the type-checking.
     */
    nr_pins = 0;
    for ( i = 0; i < dinfo->p2m_size; i++ )
    {
        if ( (pfn_type[i] & XEN_DOMCTL_PFINFO_LPINTAB) == 0 )
            continue;

        switch ( pfn_type[i] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK )
        {
        case XEN_DOMCTL_PFINFO_L1TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L1_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L2TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L2_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L3TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L3_TABLE;
            break;

        case XEN_DOMCTL_PFINFO_L4TAB:
            pin[nr_pins].cmd = MMUEXT_PIN_L4_TABLE;
            break;

        default:
            continue;
        }

        pin[nr_pins].arg1.mfn = ctx->p2m[i];
        nr_pins++;

        /* Batch full? Then flush. */
        if ( nr_pins == MAX_PIN_BATCH )
        {
            if ( xc_mmuext_op(xch, pin, nr_pins, dom) < 0 )
            {
                PERROR("Failed to pin batch of %d page tables", nr_pins);
                goto out;
            }
            nr_pins = 0;
        }
    }

    /* Flush final partial batch. */
    if ( (nr_pins != 0) && (xc_mmuext_op(xch, pin, nr_pins, dom) < 0) )
    {
        PERROR("Failed to pin batch of %d page tables", nr_pins);
        goto out;
    }

    DPRINTF("Memory reloaded (%ld pages)\n", ctx->nr_pfns);

    /* Get the list of PFNs that are not in the psuedo-phys map */
    {
        int nr_frees = 0;

        for ( i = 0; i < tailbuf.u.pv.pfncount; i++ )
        {
            unsigned long pfn = tailbuf.u.pv.pfntab[i];

            if ( ctx->p2m[pfn] != INVALID_P2M_ENTRY )
            {
                /* pfn is not in physmap now, but was at some point during
                   the save/migration process - need to free it */
                tailbuf.u.pv.pfntab[nr_frees++] = ctx->p2m[pfn];
                ctx->p2m[pfn]  = INVALID_P2M_ENTRY; /* not in pseudo-physical map */
            }
        }

        if ( nr_frees > 0 )
        {
            if ( (frc = xc_domain_decrease_reservation(xch, dom, nr_frees, 0, tailbuf.u.pv.pfntab)) != nr_frees )
            {
                PERROR("Could not decrease reservation : %d", frc);
                goto out;
            }
            else
                DPRINTF("Decreased reservation by %d pages\n", tailbuf.u.pv.pfncount);
        }
    }

    vcpup = tailbuf.u.pv.vcpubuf;
    for ( i = 0; i <= max_vcpu_id; i++ )
    {
        if ( !(vcpumap[i/64] & (1ULL << (i%64))) )
            continue;

        memcpy(ctxt, vcpup, ((dinfo->guest_width == 8) ? sizeof(ctxt->x64)
                              : sizeof(ctxt->x32)));
        vcpup += (dinfo->guest_width == 8) ? sizeof(ctxt->x64) : sizeof(ctxt->x32);

        DPRINTF("read VCPU %d\n", i);

        if ( !new_ctxt_format )
            SET_FIELD(ctxt, flags,
                      GET_FIELD(ctxt, flags, dinfo->guest_width) | VGCF_online,
                      dinfo->guest_width);

        if ( i == 0 )
        {
            /*
             * Uncanonicalise the start info frame number and poke in
             * updated values into the start info itself.
             *
             * The start info MFN is the 3rd argument to the
             * HYPERVISOR_sched_op hypercall when op==SCHEDOP_shutdown
             * and reason==SHUTDOWN_suspend, it is canonicalised in
             * xc_domain_save and therefore the PFN is found in the
             * edx register.
             */
            pfn = GET_FIELD(ctxt, user_regs.edx, dinfo->guest_width);
            if ( (pfn >= dinfo->p2m_size) ||
                 (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
            {
                ERROR("Suspend record frame number is bad");
                goto out;
            }
            mfn = ctx->p2m[pfn];
            SET_FIELD(ctxt, user_regs.edx, mfn, dinfo->guest_width);
            start_info = xc_map_foreign_range(
                xch, dom, PAGE_SIZE, PROT_READ | PROT_WRITE, mfn);
            if ( start_info == NULL )
            {
                PERROR("xc_map_foreign_range failed (for start_info)");
                goto out;
            }

            SET_FIELD(start_info, nr_pages, dinfo->p2m_size, dinfo->guest_width);
            SET_FIELD(start_info, shared_info, shared_info_frame<<PAGE_SHIFT, dinfo->guest_width);
            SET_FIELD(start_info, flags, 0, dinfo->guest_width);
            if ( GET_FIELD(start_info, store_mfn, dinfo->guest_width) > dinfo->p2m_size )
            {
                ERROR("Suspend record xenstore frame number is bad");
                munmap(start_info, PAGE_SIZE);
                goto out;
            }
            *store_mfn = ctx->p2m[GET_FIELD(start_info, store_mfn, dinfo->guest_width)];
            SET_FIELD(start_info, store_mfn, *store_mfn, dinfo->guest_width);
            SET_FIELD(start_info, store_evtchn, store_evtchn, dinfo->guest_width);
            if ( GET_FIELD(start_info, console.domU.mfn, dinfo->guest_width) > dinfo->p2m_size )
            {
                ERROR("Suspend record console frame number is bad");
                munmap(start_info, PAGE_SIZE);
                goto out;
            }
            *console_mfn = ctx->p2m[GET_FIELD(start_info, console.domU.mfn, dinfo->guest_width)];
            SET_FIELD(start_info, console.domU.mfn, *console_mfn, dinfo->guest_width);
            SET_FIELD(start_info, console.domU.evtchn, console_evtchn, dinfo->guest_width);
            munmap(start_info, PAGE_SIZE);
        }
        /* Uncanonicalise each GDT frame number. */
        if ( GET_FIELD(ctxt, gdt_ents, dinfo->guest_width) > 8192 )
        {
            ERROR("GDT entry count out of range");
            goto out;
        }

        for ( j = 0; (512*j) < GET_FIELD(ctxt, gdt_ents, dinfo->guest_width); j++ )
        {
            pfn = GET_FIELD(ctxt, gdt_frames[j], dinfo->guest_width);
            if ( (pfn >= dinfo->p2m_size) ||
                 (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
            {
                ERROR("GDT frame number %i (0x%lx) is bad", 
                      j, (unsigned long)pfn);
                goto out;
            }
            SET_FIELD(ctxt, gdt_frames[j], ctx->p2m[pfn], dinfo->guest_width);
        }
        /* Uncanonicalise the page table base pointer. */
        pfn = UNFOLD_CR3(GET_FIELD(ctxt, ctrlreg[3], dinfo->guest_width));

        if ( pfn >= dinfo->p2m_size )
        {
            ERROR("PT base is bad: pfn=%lu p2m_size=%lu type=%08lx",
                  pfn, dinfo->p2m_size, pfn_type[pfn]);
            goto out;
        }

        if ( (pfn_type[pfn] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) !=
             ((unsigned long)ctx->pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT) )
        {
            ERROR("PT base is bad. pfn=%lu nr=%lu type=%08lx %08lx",
                  pfn, dinfo->p2m_size, pfn_type[pfn],
                  (unsigned long)ctx->pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT);
            goto out;
        }
        SET_FIELD(ctxt, ctrlreg[3], FOLD_CR3(ctx->p2m[pfn]), dinfo->guest_width);

        /* Guest pagetable (x86/64) stored in otherwise-unused CR1. */
        if ( (ctx->pt_levels == 4) && (ctxt->x64.ctrlreg[1] & 1) )
        {
            pfn = UNFOLD_CR3(ctxt->x64.ctrlreg[1] & ~1);
            if ( pfn >= dinfo->p2m_size )
            {
                ERROR("User PT base is bad: pfn=%lu p2m_size=%lu",
                      pfn, dinfo->p2m_size);
                goto out;
            }
            if ( (pfn_type[pfn] & XEN_DOMCTL_PFINFO_LTABTYPE_MASK) !=
                 ((unsigned long)ctx->pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT) )
            {
                ERROR("User PT base is bad. pfn=%lu nr=%lu type=%08lx %08lx",
                      pfn, dinfo->p2m_size, pfn_type[pfn],
                      (unsigned long)ctx->pt_levels<<XEN_DOMCTL_PFINFO_LTAB_SHIFT);
                goto out;
            }
            ctxt->x64.ctrlreg[1] = FOLD_CR3(ctx->p2m[pfn]);
        }
        frc = xc_vcpu_setcontext(xch, dom, i, ctxt);
        if ( frc != 0 )
        {
            PERROR("Couldn't build vcpu%d", i);
            goto out;
        }

        if ( !ext_vcpucontext )
            goto vcpu_ext_state_restore;
        memcpy(&domctl.u.ext_vcpucontext, vcpup, 128);
        vcpup += 128;
        domctl.cmd = XEN_DOMCTL_set_ext_vcpucontext;
        domctl.domain = dom;
        frc = xc_domctl(xch, &domctl);
        if ( frc != 0 )
        {
            PERROR("Couldn't set extended vcpu%d info", i);
            goto out;
        }

 vcpu_ext_state_restore:
        if ( !vcpuextstate_size )
            continue;

        memcpy(&domctl.u.vcpuextstate.xfeature_mask, vcpup,
               sizeof(domctl.u.vcpuextstate.xfeature_mask));
        vcpup += sizeof(domctl.u.vcpuextstate.xfeature_mask);
        memcpy(&domctl.u.vcpuextstate.size, vcpup,
               sizeof(domctl.u.vcpuextstate.size));
        vcpup += sizeof(domctl.u.vcpuextstate.size);

        buffer = xc_hypercall_buffer_alloc(xch, buffer,
                                           domctl.u.vcpuextstate.size);
        if ( !buffer )
        {
            PERROR("Could not allocate buffer to restore eXtended States");
            goto out;
        }
        memcpy(buffer, vcpup, domctl.u.vcpuextstate.size);
        vcpup += domctl.u.vcpuextstate.size;

        domctl.cmd = XEN_DOMCTL_setvcpuextstate;
        domctl.domain = dom;
        domctl.u.vcpuextstate.vcpu = i;
        set_xen_guest_handle(domctl.u.vcpuextstate.buffer, buffer);
        frc = xc_domctl(xch, &domctl);
        if ( frc != 0 )
        {
            PERROR("Couldn't set eXtended States for vcpu%d", i);
            goto out;
        }
        xc_hypercall_buffer_free(xch, buffer);
    }

    memcpy(shared_info_page, tailbuf.u.pv.shared_info_page, PAGE_SIZE);

    DPRINTF("Completed checkpoint load\n");

    /* Restore contents of shared-info page. No checking needed. */
    new_shared_info = xc_map_foreign_range(
        xch, dom, PAGE_SIZE, PROT_WRITE, shared_info_frame);
    if ( new_shared_info == NULL )
    {
        PERROR("xc_map_foreign_range failed (for new_shared_info)");
        goto out;
    }

    /* restore saved vcpu_info and arch specific info */
    MEMCPY_FIELD(new_shared_info, old_shared_info, vcpu_info, dinfo->guest_width);
    MEMCPY_FIELD(new_shared_info, old_shared_info, arch, dinfo->guest_width);

    /* clear any pending events and the selector */
    MEMSET_ARRAY_FIELD(new_shared_info, evtchn_pending, 0, dinfo->guest_width);
    for ( i = 0; i < XEN_LEGACY_MAX_VCPUS; i++ )
	    SET_FIELD(new_shared_info, vcpu_info[i].evtchn_pending_sel, 0, dinfo->guest_width);

    /* mask event channels */
    MEMSET_ARRAY_FIELD(new_shared_info, evtchn_mask, 0xff, dinfo->guest_width);

    /* leave wallclock time. set by hypervisor */
    munmap(new_shared_info, PAGE_SIZE);

    /* Uncanonicalise the pfn-to-mfn table frame-number list. */
    for ( i = 0; i < P2M_FL_ENTRIES; i++ )
    {
        pfn = p2m_frame_list[i];
        if ( (pfn >= dinfo->p2m_size) || (pfn_type[pfn] != XEN_DOMCTL_PFINFO_NOTAB) )
        {
            ERROR("PFN-to-MFN frame number %i (%#lx) is bad", i, pfn);
            goto out;
        }
        p2m_frame_list[i] = ctx->p2m[pfn];
    }

    /* Copy the P2M we've constructed to the 'live' P2M */
    if ( !(ctx->live_p2m = xc_map_foreign_pages(xch, dom, PROT_WRITE,
                                           p2m_frame_list, P2M_FL_ENTRIES)) )
    {
        PERROR("Couldn't map p2m table");
        goto out;
    }

    /* If the domain we're restoring has a different word size to ours,
     * we need to adjust the live_p2m assignment appropriately */
    if ( dinfo->guest_width > sizeof (xen_pfn_t) )
        for ( i = dinfo->p2m_size - 1; i >= 0; i-- )
            ((int64_t *)ctx->live_p2m)[i] = (long)ctx->p2m[i];
    else if ( dinfo->guest_width < sizeof (xen_pfn_t) )
        for ( i = 0; i < dinfo->p2m_size; i++ )   
            ((uint32_t *)ctx->live_p2m)[i] = ctx->p2m[i];
    else
        memcpy(ctx->live_p2m, ctx->p2m, dinfo->p2m_size * sizeof(xen_pfn_t));
    munmap(ctx->live_p2m, P2M_FL_ENTRIES * PAGE_SIZE);

    frc = xc_dom_gnttab_seed(xch, dom, *console_mfn, *store_mfn,
                             console_domid, store_domid);
    if (frc != 0)
    {
        ERROR("error seeding grant table");
        goto out;
    }

    DPRINTF("Domain ready to be built.\n");
    rc = 0;
    goto out;

  finish_hvm:

    /* Dump the QEMU state to a state file for QEMU to load */
    if ( dump_qemu(xch, dom, &tailbuf.u.hvm) ) {
        PERROR("Error dumping QEMU state to file");
        goto out;
    }

    /* These comms pages need to be zeroed at the start of day */
    if ( xc_clear_domain_page(xch, dom, tailbuf.u.hvm.magicpfns[0]) ||
         xc_clear_domain_page(xch, dom, tailbuf.u.hvm.magicpfns[1]) ||
         xc_clear_domain_page(xch, dom, tailbuf.u.hvm.magicpfns[2]) )
    {
        PERROR("error zeroing magic pages");
        goto out;
    }

    if ( (frc = xc_hvm_param_set(xch, dom,
                                 HVM_PARAM_IOREQ_PFN, tailbuf.u.hvm.magicpfns[0]))
         || (frc = xc_hvm_param_set(xch, dom,
                                    HVM_PARAM_BUFIOREQ_PFN, tailbuf.u.hvm.magicpfns[1]))
         || (frc = xc_hvm_param_set(xch, dom,
                                    HVM_PARAM_STORE_PFN, tailbuf.u.hvm.magicpfns[2]))
         || (frc = xc_hvm_param_set(xch, dom,
                                    HVM_PARAM_PAE_ENABLED, pae))
         || (frc = xc_hvm_param_set(xch, dom,
                                    HVM_PARAM_STORE_EVTCHN,
                                    store_evtchn)) )
    {
        PERROR("error setting HVM params: %i", frc);
        goto out;
    }
    *store_mfn = tailbuf.u.hvm.magicpfns[2];

    if ( console_pfn ) {
        if ( xc_clear_domain_page(xch, dom, console_pfn) ) {
            PERROR("error zeroing console page");
            goto out;
        }
        if ( (frc = xc_hvm_param_set(xch, dom,
                                    HVM_PARAM_CONSOLE_PFN, console_pfn)) ) {
            PERROR("error setting HVM param: %i", frc);
            goto out;
        }
        *console_mfn = console_pfn;
    }

    frc = xc_domain_hvm_setcontext(xch, dom, tailbuf.u.hvm.hvmbuf,
                                   tailbuf.u.hvm.reclen);
    if ( frc )
    {
        PERROR("error setting the HVM context");
        goto out;
    }

    frc = xc_dom_gnttab_hvm_seed(xch, dom, *console_mfn, *store_mfn,
                                 console_domid, store_domid);
    if (frc != 0)
    {
        ERROR("error seeding grant table");
        goto out;
    }

    if ( ctx->lazy )
    {
        /*
         * Start a pager here. We double fork to create a daemon pager
         * to serve the pagefault requests of the lazy restore pager.
         */
        pid_t pid1, pid2;
        int status;
        int pipe_c2p[2] = { 0,0 }; /* pipe child to parent. */

        /*
         * set rc <0 so that if we get any error than we revert back
         * to the conventional restore process by jumping to pager_out.
         */
        rc = -1;

        if ( pipe(pipe_c2p) == -1 )
        {
            PERROR("Error setting up pager pipes");
            goto pager_out;
        }

        pid1 = fork();
        if( pid1 )
        {
            char buf[80];
            int exit_code = 1;
            memset(buf, 0, sizeof(buf));

            /* Wait for the first child to exit. */
            waitpid(pid1, &status, 0);
            if ( WIFEXITED(status) )
            {
                exit_code = WEXITSTATUS(status);
                DPRINTF("restore pager first child exited,"
                        " status=%d\n", exit_code);
            }
            if ( exit_code != 0 )
            {
                PERROR("restore pager first child exited with error");
                goto pager_out;
            }

            /* We only need to listen from child so close write end of pipe. */
            close( pipe_c2p[1] );

            /* Wait for the pager (grand child) to give us sign to continue */
            rc = read(pipe_c2p[0], buf, sizeof(buf)); /* Blocking Call */
            if( rc < 0 )
            {
                PERROR("Error while reading child status from pipe");
            }
            else if( strncmp(LAZY_RESTORE_PAGER_SUCCESS, buf,
                             strlen(LAZY_RESTORE_PAGER_SUCCESS)) == 0 )
            {
                DPRINTF("Pager setup successful");
            }
            else if( strncmp(LAZY_RESTORE_PAGER_FAILURE, buf,
                             strlen(LAZY_RESTORE_PAGER_FAILURE)) == 0 )
            {
                PERROR("Pager setup failed. "
                       "Please check pager logs for details");
                rc = -1; /* Set rc<0 so we can fallback to normal restore */
                goto pager_out;
            }
            DPRINTF("Read %s from the pager rc is %d",buf,rc);

            /* close the other end (read) of pipe too. */
            close ( pipe_c2p[0] );
            goto out;
        }
        else if ( pid1 == 0 ) /* first child process */
        {
            pid2 = fork();
            if( pid2 )
            {
                exit(0);
            }
            else if ( pid2 == 0 ) /* second child process */
            {
                lazy_restore_pager_daemon(xch, ctx, &pagebuf,
                                          &tailbuf, io_fd, dom, pipe_c2p);
            }
            else
            {
                /*
                 * Failed to double fork while setting up the pager process,
                 * exit the child process with failed status to notify the
                 * parent process to revert back to normal restore process.
                 */
                PERROR("doublefork failed while setting up pager");
                exit(1);
            }
        }
        else
        {
            /* Lazy restore pager process fork failed, revert back. */
            PERROR("fork failed while setting up pager");
            goto pager_out;
        }
    }

    /* HVM success! */
    rc = 0;

  pager_out:
    if ( ctx->lazy ) /* Just in case we don't fall here from any other path. */
    {
        /*
         * If we get some error while setting up the lazy restore pager
         * than we cleanup the lazy pager data and try to restore the
         * domain using non lazy approach.
         */

        /* Clear the hashtable */
        if( pagebuf.pfn_to_fileoffset )
        {
            /* Tell the hashtable to free memory, so we pass second arg 1.*/
            hashtable_destroy(pagebuf.pfn_to_fileoffset,1);
            pagebuf.pfn_to_fileoffset = NULL;
        }

        if ( rc < 0 )
        {
            /*
             * Error. Clear the lazy flag and revert back
             * to continue with normal restore.
             */
            PERROR("Creation of restore pager failed."
                   " Revert back to normal restore process");
            ctx->lazy = 0;
            ctx->completed = 0;
            ctx->pager_fallback = 1;

            if ( saved_offset )
            {
                off_t temp_offset;

                temp_offset = lseek(io_fd, saved_offset , SEEK_SET);
                if ( temp_offset < 0 || temp_offset != saved_offset )
                {
                    PERROR("ERROR problem while restoring file offset");
                    rc = -1;
                    goto out;
                }
            }
            goto loadpages;
        }
    }

 out:
    if ( (rc != 0) && (dom != 0) )
        xc_domain_destroy(xch, dom);

    /* Perform libxl callback before exiting. */
    rc = do_callback(xch, dom, &tdata, callbacks);

    xc_hypercall_buffer_free(xch, ctxt);
    free(mmu);
    free(ctx->p2m);
    free(pfn_type);
    free(region_mfn);
    free(ctx->p2m_batch);
    pagebuf_free(&pagebuf);
    tailbuf_free(&tailbuf);

    /* discard cache for save file  */
    discard_file_cache(xch, io_fd, 1 /*flush*/);

    fcntl(io_fd, F_SETFL, orig_io_fd_flags);

    DPRINTF("Restore exit of domid %u with rc=%d\n", dom, rc);

    return rc;
}

/*
 * Local variables:
 * mode: C
 * c-file-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
