---
layout: post
title: Jemalloc Size Classes
date: 2022-01-15 15:48:56
id: b9e2959cb277be89f9db097133c00fe3
tags:
  - [Computer Science, Memory Analysis, Jemalloc]
---

# 概述

如下图所示：

+ jemalloc 有三种类型的 size class groups 。
+ regular group 有多组。
+ 每组 size class group 又包含多个 size classes 。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/jemalloc-size-classes/size-class.png)

|        group         | index | lg\_base | lg\_delta | ndelta |  psz  | bin  | pgs  | lg\_delta\_lookup | size |
| :------------------: | :---: | :-----:  | :------:  | :----: | :---: | :--: | :--: |  :-------------:  | :-:  |
|  Tiny size classes   |       |          |           |        |       |      |      |                   |      |
|                      |   0   |    3     |     3     |   0    | false | true |  1   |         3         |  8   |
|                      |   1   |    3     |     3     |   1    | false | true |  1   |         3         |  16  |
| Initial pseudo-group |       |          |           |        |       |      |      |                   |      |
|                      |   2   |    4     |     4     |   1    | false | true |  1   |         4         |  32  |
|                      |   3   |    4     |     4     |   2    | false | true |  3   |         4         |  48  |
|                      |   4   |    4     |     4     |   3    | false | true |  1   |         4         |  64  |
|   Regular group 0    |       |          |           |        |       |      |      |                   |      |
|                      |   5   |    6     |     4     |   1    | false | true |  5   |         4         |  80  |
|                      |   6   |    6     |     4     |   2    | false | true |  3   |         4         |  96  |
|                      |   7   |    6     |     4     |   3    | false | true |  7   |         4         | 112  |
|                      |   8   |    6     |     4     |   4    | false | true |  1   |         4         | 128  |
|   Regular group 1    |       |          |           |        |       |      |      |                   |      |
|                      |   9   |    7     |     5     |   1    | false | true |  5   |         5         | 160  |
|                      |  10   |    7     |     5     |   2    | false | true |  3   |         5         | 192  |
|                      |  11   |    7     |     5     |   3    | false | true |  7   |         5         | 224  |
|                      |  12   |    7     |     5     |   4    | false | true |  1   |         5         | 256  |
|   Regular group 2    |       |          |           |        |       |      |      |                   |      |
|                      |  13   |    8     |     6     |   1    | false | true |  5   |         6         | 320  |
|                      |  14   |    8     |     6     |   2    | false | true |  3   |         6         | 384  |
|                      |  15   |    8     |     6     |   3    | false | true |  7   |         6         | 448  |
|                      |  16   |    8     |     6     |   4    | false | true |  1   |         6         | 512  |
|   Regular group 3    |       |          |           |        |       |      |      |                   |      |
|                      |  17   |    9     |     7     |   1    | false | true |  5   |         7         | 640  |
|                      |  18   |    9     |     7     |   2    | false | true |  3   |         7         | 768  |
|                      |  19   |    9     |     7     |   3    | false | true |  7   |         7         | 896  |
|                      |  20   |    9     |     7     |   4    | false | true |  1   |         7         | 1024 |
|   Regular group 4    |       |          |           |        |       |      |      |                   |      |
|                      |  21   |    10    |     8     |   1    | false | true |  5   |         8         | 1280 |
|                      |  22   |    10    |     8     |   2    | false | true |  3   |         8         | 1536 |
|                      |  23   |    10    |     8     |   3    | false | true |  7   |         8         | 1792 |
|                      |  24   |    10    |     8     |   4    | false | true |  1   |         8         | 2048 |
|   Regular group 5    |       |          |           |        |       |      |      |                   |      |
|                      |  25   |    11    |     9     |   1    | false | true |  5   |         9         | 2560 |
|                      |  26   |    11    |     9     |   2    | false | true |  3   |         9         | 3072 |
|                      |  27   |    11    |     9     |   3    | false | true |  7   |         9         | 3584 |
|                      |  28   |    11    |     9     |   4    | true  | true |  1   |         9         | 4096 |
|   Regular group 6    |       |          |           |        |       |      |      |                   |      |
|                      |  29   |    12    |    10     |   1    | false | true |  5   |         0         | 5120 |
|                      |  30   |    12    |    10     |   2    | false | true |  3   |         0         | 6144 |
|                      |  31   |    12    |    10     |   3    | false | true |  7   |         0         | 7168 |
|                      |  32   |    12    |    10     |   4    | true  | true |  2   |         0         | 8192 |

[jemalloc/include/jemalloc/internal/sc.h](https://github.com/jemalloc/jemalloc/blob/ea6b3e973b477b8061e0076bb257dbd7f3faa756/include/jemalloc/internal/sc.h#L6) 的注释详细地描述了三种类型的 size class group 是如何产生的：

+ regular group 的产生非常简单，每一组 regular group 都覆盖一个左开右闭区间 (base, base * 2\] ，这个区间会被划分为 `pow(2, SC_LG_NGROUP)` 个等宽区间。
+ 对于 base = 16 的情况，将 (16, 32] 分成 `pow(2, SC_LG_NGROUP) = 4` 个等宽区间，得到 (16, 20] / (20, 24] / (24, 28] / (28, 32] 。如果我们将一个内存页切分成多个连续的、大小相同的 objects ，那么部分大小为 20 bytes 的 objects 的起始地址不能对齐到 `pow(2, LG_QUANTUM) = 16` 个字节。所以对这部分区间要做特殊处理，从而产生 initial pseudo-group  ，initial pseudo-group 内的每两个相邻的 size classes 相距 `pow(2, LG_QUANTUM) = 16` 个字节。
+ 对于「大小」小于「对齐要求」（即 `pow(2, LG_QUANTUM) = 16` 字节）的 objects ，jemalloc 在分配它们时不会考虑对齐，从而产生 tiny size classes 。Tiny size classes 中任意两个连续的 size classes 是两倍的关系。

# size class 的数学性质

通过对 `SC_LG_NGROUP` 等参数的巧妙限制，jemalloc 保证「size class」的大小等于 `(ZU(1) << sc->lg_base) + (ZU(sc->ndelta) << sc->lg_delta)` 。

# 初始化 size class

```c
static void
size_class(
    // Output.
    sc_t *sc,
    // pow(2, lg_max_lookup) 是 object 的大小上限，默认值是 4KiB 。
    // 更大的 malloc 请求会直接分配整页内存页？
    int lg_max_lookup,
    // pow(2, lg_page) 是一页内存的大小，默认值是 4KiB 。
    int lg_page,
    // pow(2, lg_ngroup) 是一组 regular group 分成的区间数，默认值是 4 。
    int lg_ngroup,
    // size class 的序号，从 0 开始自增。
    int index,
    // object size = (1 << lg_base) + ndelta * (1 << lg_delta)
    int lg_base,
    int lg_delta,
    int ndelta) {
    // Trivial assignments.
    sc->index = index;
    sc->lg_base = lg_base;
    sc->lg_delta = lg_delta;
    sc->ndelta = ndelta;
    // reg_size_compute(lg_base, lg_delta, ndelta) = object size
    // True if the size class is a multiple of the page size,
    // false otherwise.
    sc->psz = (reg_size_compute(lg_base, lg_delta, ndelta)
        % (ZU(1) << lg_page) == 0);
    size_t size = (ZU(1) << lg_base) + (ZU(ndelta) << lg_delta);
    // 为什么 small size class 的定义这么奇怪？
    // We declare a size class is binnable if size < page size * group.
    // https://github.com/jemalloc/jemalloc/blob/ea6b3e973b477b8061e0076bb257dbd7f3faa756/include/jemalloc/internal/sc.h#L229
    if (size < (ZU(1) << (lg_page + lg_ngroup))) {
        // True if the size class is a small, bin, size class.
        // False otherwise.
        sc->bin = true;
        // The slab page count if a small bin size class, 0 otherwise.
        // 为了避免内存浪费，(pgs * pow(2, lg_page)) % size == 0 。
        sc->pgs = slab_size(lg_page, lg_base, lg_delta, ndelta);
    } else {
        sc->bin = false;
        sc->pgs = 0;
    }
    if (size <= (ZU(1) << lg_max_lookup)) {
        // Same as lg_delta if a lookup table size class, 0 otherwise.
        sc->lg_delta_lookup = lg_delta;
    } else {
        sc->lg_delta_lookup = 0;
    }
}
```

# 查找 size class

`sz_size2index_tab` 是一张 lookup table ，能加速从「request size」到 size class 的查找过程：

+ `sz_size2index_lookup` 是查找函数。
+ `sz_boot_size2index_tab` 是初始化 lookup table 的函数。

| size range | id = (size + the tiny min size - 1) / the tiny min size (8) | size class | size class size |
|    :-:     |                             :-:                             |    :-:     |       :-:       |
|   [0, 0]   |                              0                              |            |                 |
|   (0, 8]   |                              1                              |     0      |        8        |
|  (8, 16]   |                              2                              |     1      |       16        |
|  (16, 24]  |                              3                              |     2      |       32        |
|  (24, 32]  |                              4                              |     2      |       32        |
|  (32, 40]  |                              5                              |     3      |       48        |
|  (40, 48]  |                              6                              |     3      |       48        |
|  (48, 56]  |                              7                              |     4      |       64        |
|  (56, 64]  |                              8                              |     4      |       64        |
|  (64, 72]  |                              9                              |     5      |       80        |
|  (72, 80]  |                             10                              |     5      |       80        |

```c
/*
 * To keep this table small, we divide sizes by the tiny min size, which gives
 * the smallest interval for which the result can change.
 */
JEMALLOC_ALIGNED(CACHELINE)
uint8_t sz_size2index_tab[(SC_LOOKUP_MAXCLASS >> SC_LG_TINY_MIN) + 1];

JEMALLOC_ALWAYS_INLINE szind_t
sz_size2index_lookup(size_t size) {
    assert(size <= SC_LOOKUP_MAXCLASS);
    szind_t ret = (sz_size2index_tab[(size + (ZU(1) << SC_LG_TINY_MIN) - 1)
                     >> SC_LG_TINY_MIN]);
    assert(ret == sz_size2index_compute(size));
    return ret;
}

static void
sz_boot_size2index_tab(const sc_data_t *sc_data) {
    size_t dst_max = (SC_LOOKUP_MAXCLASS >> SC_LG_TINY_MIN) + 1;
    size_t dst_ind = 0;
    for (unsigned sc_ind = 0; sc_ind < SC_NSIZES && dst_ind < dst_max;
        sc_ind++) {
        const sc_t *sc = &sc_data->sc[sc_ind];
        size_t sz = (ZU(1) << sc->lg_base)
            + (ZU(sc->ndelta) << sc->lg_delta);
        // index = sc_ind 的 size class 能覆盖的最大 size 就是 sz 。
        size_t max_ind = ((sz + (ZU(1) << SC_LG_TINY_MIN) - 1)
                   >> SC_LG_TINY_MIN);
        for (; dst_ind <= max_ind && dst_ind < dst_max; dst_ind++) {
            sz_size2index_tab[dst_ind] = sc_ind;
        }
    }
}
```
