---
layout: post
title: jemalloc-cache-bin
date: 2022-01-31 23:17:25
tags:
---

```c
struct cache_bin_s {
  /* Min # cached since last GC. */
  cache_bin_sz_t low_water;
  /* # of cached objects. */
  cache_bin_sz_t ncached;
  /*
   * ncached and stats are both modified frequently.  Let's keep them
   * close so that they have a higher chance of being on the same
   * cacheline, thus less write-backs.
   */
  cache_bin_stats_t tstats;
  /*
   * Stack of available objects.
   *
   * To make use of adjacent cacheline prefetch, the items in the avail
   * stack goes to higher address for newer allocations.  avail points
   * just above the available space, which means that
   * avail[-ncached, ... -1] are available items and the lowest item will
   * be allocated first.
   */
  // avail 是一个数组，它的下标是 [-ncached, ... -1] 。
  // 第一个元素是 *(avail - ncached) ，最后一个元素是 *(avail - 1) 。
  void **avail;
}
```

```c
JEMALLOC_ALWAYS_INLINE void *
cache_bin_alloc_easy(cache_bin_t *bin, bool *success) {
  void *ret;
  bin->ncached--;

  /*
   * Check for both bin->ncached == 0 and ncached < low_water
   * in a single branch.
   */
  if (unlikely(bin->ncached <= bin->low_water)) {
    bin->low_water = bin->ncached;
    if (bin->ncached == -1) {
      bin->ncached = 0;
      *success = false;
      return NULL;
    }
  }

  /*
   * success (instead of ret) should be checked upon the return of this
   * function.  We avoid checking (ret == NULL) because there is never a
   * null stored on the avail stack (which is unknown to the compiler),
   * and eagerly checking ret would cause pipeline stall (waiting for the
   * cacheline).
   */
  *success = true;
  ret = *(bin->avail - (bin->ncached + 1));
  return ret;
}
```

1. 填充顺序与使用顺序相反
2. 尽量让使用过程可以利用到 cacheline prefetch

```c
void arena_tcache_fill_small(tsdn_t *tsdn, arena_t *arena, tcache_t *tcache,
  cache_bin_t *tbin, szind_t binind, uint64_t prof_accumbytes) {
  unsigned cnt;

  assert(tbin->ncached == 0);

  unsigned binshard;
  bin_t *bin = arena_bin_choose_lock(tsdn, arena, binind, &binshard);

  unsigned nfill = (tcache_bin_info[binind].ncached_max >>
    tcache->lg_fill_div[binind]);
  for (unsigned i = 0; i < nfill; i += cnt) {
    extent_t *slab;
    if ((slab = bin->slabcur) != NULL && extent_nfree_get(slab) > 0) {
      unsigned tofill = nfill - i;
      cnt = tofill < extent_nfree_get(slab) ? tofill : extent_nfree_get(slab);
      arena_slab_reg_alloc_batch(slab,
                                 &bin_infos[binind],
                                 cnt,
                                 tbin->avail - nfill + i);
    } else {
      cnt = 1;
      void *ptr = arena_bin_malloc_hard(tsdn, arena, bin, binind, binshard);
      /*
       * OOM.  tbin->avail isn't yet filled down to its first
       * element, so the successful allocations (if any) must
       * be moved just before tbin->avail before bailing out.
       */
      if (ptr == NULL) {
        if (i > 0) {
          memmove(tbin->avail - i, tbin->avail - nfill, i * sizeof(void *));
        }
        break;
      }
      /* Insert such that low regions get used first. */
      // 当走到该分支时，jemalloc 会从前往后填充 tbin->avail 数组。
      // | avail - nfill | avail - nfill + 1 | avail - nfill + 2 | ... |
      *(tbin->avail - nfill + i) = ptr;
    }
  }
  malloc_mutex_unlock(tsdn, &bin->lock);
  tbin->ncached = i;
  arena_decay_tick(tsdn, arena);
}
```

```c
static void arena_slab_reg_alloc_batch(extent_t *slab,
                                       const bin_info_t *bin_info,
                                       unsigned cnt,
                                       void** ptrs) {
  while (i < cnt) {
    uintptr_t base = (uintptr_t)extent_addr_get(slab);
    uintptr_t regsize = (uintptr_t)bin_info->reg_size;
    while (pop--) {
      size_t bit = cfs_lu(&g);
      size_t regind = shift + bit;
      *(ptrs + i) = (void *)(base + regsize * regind);
      i++;
    }
  }
}
```

```bash
(gdb) b 324
Breakpoint 2 at 0x555555578b44: file ../src/arena.c, line 324.
# 不断交替执行 continue 和 p/x {base, regsize, regind} 。
$4  = {0x7ffff641e000, 0x50, 0x1}
$5  = {0x7ffff641e000, 0x50, 0x2}
$6  = {0x7ffff641e000, 0x50, 0x3}
$7  = {0x7ffff641e000, 0x50, 0x4}
$8  = {0x7ffff641e000, 0x50, 0x5}
$9  = {0x7ffff641e000, 0x50, 0x6}
$10 = {0x7ffff641e000, 0x50, 0x7}
$11 = {0x7ffff641e000, 0x50, 0x8}
$12 = {0x7ffff641e000, 0x50, 0x9}
$13 = {0x7ffff641e000, 0x50, 0xa}
```

从 GDB 的结果可以得知，`arena_slab_reg_alloc_batch` 在填充 `tbin->avail` 时保证基址低的 objects 在前，基址高的 objects 在后。

严谨地推导上述结论需要了解有关于 `extents_s::bitmap` ，`popcount_lu` 和 `cfs_lu` 的知识：

+  `extend_s::bitmap`
  +
