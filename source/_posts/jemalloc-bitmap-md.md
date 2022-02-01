---
layout: post
title: jemalloc-bitmap.md
date: 2022-02-01 13:23:04
tags:
---

[jemalloc/include/jemalloc/internal/bitmap.h](https://github.com/jemalloc/jemalloc/blob/e904f813b40b4286e10172163c880fd9e1d0608a/include/jemalloc/internal/bitmap.h)

|             var              |                             expression                              | val |                                           reason                                           |
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
| BITMAP_GROUPS_x_LEVEL(nbits) |                                                                     |     |            用 x 层的 bitmap 去表达 nbits 个元素是否存在，需要多少个 long 型数？            |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/jemalloc-bitmap/hierarchical-bitmap.drawio.png)
