---
layout: post
title: jemalloc-bitmap.md
date: 2022-02-01 13:23:04
tags:
---

[jemalloc/include/jemalloc/internal/bitmap.h](https://github.com/jemalloc/jemalloc/blob/e904f813b40b4286e10172163c880fd9e1d0608a/include/jemalloc/internal/bitmap.h)

|             var              |                             expression                              | val |                                        description                                         |
|             :-:              |                                 :-:                                 | :-: |                                            :-:                                             |
|       LG_SIZEOF_BITMAP       |                           LG_SIZEOF_LONG                            |  3  |                                 lg(sizeof(long) in bytes)                                  |
|    LG_BITMAP_GROUP_NBITS     |                        LG_SIZEOF_BITMAP + 3                         |  6  |                                  lg(sizeof(long) in bits)                                  |
|      BITMAP_GROUP_NBITS      |                     1 << LG_BITMAP_GROUP_NBITS                      | 64  |                                    sizeof(long) in bits                                    |
|   BITMAP_GROUP_NBITS_MASK    |                       BITMAP_GROUP_NBITS - 1                        | 63  |                                                                                            |
|  BITMAP_BITS2GROUPS(nbits)   |     ((nbits) + BITMAP_GROUP_NBITS - 1) >> LG_BITMAP_GROUP_NBITS     |     | 需要多少个 long 类型数，才能存储 nbits 个 bits ？`+ BITMAP_GROUP_NBITS - 1` 是在向上取整。 |
|   BITMAP_GROUPS_L0(nbits)    |                      BITMAP_BITS2GROUPS(nbits)                      |     |                                                                                            |
|   BITMAP_GROUPS_L1(nbits)    |            BITMAP_BITS2GROUPS(BITMAP_BITS2GROUPS(nbits)             |     |                                                                                            |
|   BITMAP_GROUPS_L2(nbits)    | BITMAP_BITS2GROUPS(BITMAP_BITS2GROUPS(BITMAP_BITS2GROUPS((nbits)))) |     |                                                                                            |
|   BITMAP_GROUPS_Lx(nbits)    |                                                                     |     |                                                                                            |
| BITMAP_GROUPS_1_LEVEL(nbits) |                       BITMAP_GROUPS_L0(nbits)                       |     |                                                                                            |
| BITMAP_GROUPS_2_LEVEL(nbits) |       BITMAP_GROUPS_1_LEVEL(nbits) + BITMAP_GROUPS_L1(nbits)        |     |                                                                                            |
| BITMAP_GROUPS_x_LEVEL(nbits) |                                                                     |     |      如下图所示，用 x 层的 bitmap 去表达 nbits 个元素是否存在，需要多少个 long 型数？      |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/jemalloc-bitmap/hierarchical-bitmap.drawio.png)

|                    var                    |                expression                | val |                                                                                     description                                                                                     |
|                    :-:                    |                   :-:                    | :-: |                                                                                         :-:                                                                                         |
|                 SC_NTINY                  |                                          |  1  |                                                                                                                                                                                     |
|                SC_NPSEUDO                 |                                          |  4  |                                                                                                                                                                                     |
|                SC_NREGULAR                |                                          | 227 |                                             参考 [Jemalloc Size Classes]() ，SC_NREGULAR 是属于 regular groups 的 size classes 的数量。                                             |
|                 SC_NSIZES                 |   SC_NTINY + SC_NPSEUDO + SC_NREGULAR    | 232 |                                                                                                                                                                                     |
|                  LG_PAGE                  |                                          | 12  |                                                                               内存页的大小是 4KiB 。                                                                                |
|              SC_LG_TINY_MIN               |                                          |  3  |                                       参考 [Jemalloc Size Classes]() ，SC_LG_TINY_MIN 是 3 ，jemalloc 最小的对象大小是 pow(2, 3) = 8 个字节。                                       |
|              LG_SLAB_MAXREGS              |        (LG_PAGE - SC_LG_TINY_MIN)        |  9  |                                                                          一页内存页最多存多少个 objects ？                                                                          |
|             LG_BITMAP_MAXBITS             | MAX(LG_SLAB_MAXREGS, LG_CEIL(SC_NSIZES)) |  9  | 为什么需要考虑 LG_CEIL(SC_NSIZES) ？[jemalloc: Use a bitmap in extents_t to speed up search.](https://github.com/jemalloc/jemalloc/commit/5d33233a5e6601902df7cddd8cc8aa0b135c77b2) |
| LG_BITMAP_MAXBITS - LG_BITMAP_GROUP_NBITS |                  9 - 6                   |  3  |                                                                            没有定义 BITMAP_USE_TREE 宏。                                                                            |

bitmap 是只有 extends 一个人用吗？不然为什么决策要不要用树的地方放在 macro ？

[GCC](https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html) 提供了内建函数 `__builtin_ffsl` ，入参是 `long x` ，返回值是入参 `x` 中「位于最低位且为 1 的 bit 」的下标 + 1 ：

> Returns one plus the index of the least significant 1-bit of x, or if x is zero, returns zero.

jemalloc 利用该函数实现了 bitmap 的查找操作 find first unset >= bit ，由于 GCC 提供的函数是 `__builtin_ffsl` ，所以 jemalloc 只能把 1 当做 unset ，把 0 当做 set（这违背了我们的直觉）：

```c
/* ffu: find first unset >= bit. */
static inline size_t
bitmap_ffu(const bitmap_t *bitmap, const bitmap_info_t *binfo, size_t min_bit) {
  assert(min_bit < binfo->nbits);
  // goff: group offset.
  size_t goff = min_bit >> LG_BITMAP_GROUP_NBITS;
  bitmap_t g = bitmap[goff] & ~((1LU << (min_bit & BITMAP_GROUP_NBITS_MASK)) - 1);
  size_t bit;
  do {
      bit = ffs_lu(g); // Call __builtin_ffsl inside.
      if (bit != 0) {
        return (goff << LG_BITMAP_GROUP_NBITS) + (bit - 1);
      }
      goff++;
      g = bitmap[goff];
  } while (goff < binfo->ngroups);
  return binfo->nbits;
}
```

`bitmap_set` 同样将 1 当做 unset ，将 0 当做 set ：

```c
static inline void bitmap_set(bitmap_t *bitmap,
                              const bitmap_info_t *binfo,
                              size_t bit) {
  assert(bit < binfo->nbits);
  assert(!bitmap_get(bitmap, binfo, bit));
  size_t goff = bit >> LG_BITMAP_GROUP_NBITS;
  bitmap_t* gp = &bitmap[goff];
  bitmap_t g = *gp;
  // 验证指定的 bit 是 1 ，即处于 unset 状态。
  assert(g & (ZU(1) << (bit & BITMAP_GROUP_NBITS_MASK)));
  // 将指定的 bit 翻转成 0 ，其余 bits 不变，即置成 unset 状态。
  // 1 ^ 1 = 0
  // 1 ^ 0 = 1
  // 0 ^ 1 = 1
  // 0 ^ 0 = 0
  g ^= ZU(1) << (bit & BITMAP_GROUP_NBITS_MASK);
  *gp = g;
  assert(bitmap_get(bitmap, binfo, bit));
}
```

`sz_psz2ind` 晦涩难懂，我们需要翻看它的历史才能理解它：

+ [Implement pz2ind(), pind2sz(), and psz2u().](https://github.com/jemalloc/jemalloc/commit/226c44697)

  > These compute size classes and indices similarly to `size2index()`, `index2size()` and `s2u()`, respectively, but using the subset of size classes that are multiples of the page size. Note that `pszind_t` and `szind_t` are not interchangeable.

+ [Fix psz/pind edge cases.](https://github.com/jemalloc/jemalloc/commit/ea9961acd)

  > Add an "over-size" extent heap in which to store extents which exceed the maximum size class (plus cache-oblivious padding, if enabled). Remove `psz2ind_clamp()` and use `psz2ind()` instead so that trying to allocate the maximum size class can in principle succeed. In practice, this allows assertions to hold so that OOM errors can be successfully generated.

```c
JEMALLOC_ALWAYS_INLINE pszind_t(size_t psz) {
  if (unlikely(psz > SC_LARGE_MAXCLASS)) {
    return SC_NPSIZES;
  }
  // pow(2, x - 1) < psz <= pow(2, x)
  pszind_t x = lg_floor((psz << 1) - 1);
  // first_ps_rg: first page size regular group.
  // The range of first_ps_rg is (base, base * 2],
  // and base == pow(2, LG_PAGE) * pow(2, SC_LG_NGROUP).
  // Each size class in or after first_ps_rg
  // is an integer multiple of pow(2, LG_PAGE).
  // off_to_first_ps_rg is begin from 1, instead of 0.
  pszind_t off_to_first_ps_rg = (x < SC_LG_NGROUP + LG_PAGE) ?
    0 : x - (SC_LG_NGROUP + LG_PAGE);

  // Same as sc_s::lg_delta.
  // For regular group r, lg_delta(r) - regular_group_index(r) == Constant.
  // lg_delta(r) - rg_ind(r) == lg_delta(first_ps_rg) - rg_ind(first_ps_rg)
  // lg_delta(r) = lg_delta(first_ps_rg) + (rg_ind(r) - rg_ind(first_ps_rg))
  //             = lg_delta(first_pg_rg) + (shift_to_first_ps_rg - 1)
  //             = LG_PAGE + ((x - (SC_LG_NGROUP + LG_PAGE)) - 1)
  //             = x - SC_LG_NGROUP - 1
  pszind_t lg_delta = (x < SC_LG_NGROUP + LG_PAGE + 1) ?
    LG_PAGE : x - SC_LG_NGROUP - 1;
  // |xxxxxxxxx|-------------------------|xxxxxxxxx|
  //           |<--      ndelta       -->|
  //           |<-- len: SC_LG_NGROUP -->|
  //        lg_base                  lg_delta
  // rg_inner_off = ndelta - 1
  // Why use (psz - 1)? Handle case: psz % pow(2, lg_delta) == 0.
  size_t delta_inverse_mask = ZU(-1) << lg_delta;
  pszind_t rg_inner_off = (((((psz - 1) & delta_inverse_mask) >> lg_delta)) &
    ((ZU(1) << SC_LG_NGROUP) - 1));

  pszind_t base_ind = off_to_first_ps_rg << SC_LG_NGROUP;
  pszind_t ind = base_ind + rg_inner_off;
  return ind;
}
```
