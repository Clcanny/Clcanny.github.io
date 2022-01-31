---
layout: post
title: jemalloc-tls
date: 2022-01-22 23:53:07
tags:
---

# 阅读源码的一些假设

## 假设 jemalloc 不绑核

根据 [Linux Documentation: sched_getcpu](https://linux.die.net/man/3/sched_getcpu) 和 [Linux Documentation: getcpu](https://linux.die.net/man/2/getcpu) 的说法，linux kernel 2.6.19 / glibc 2.6 及以上版本均支持 `sched_getcpu` 函数：

> This function is available since glibc 2.6.
>
> `getcpu()` was added in kernel 2.6.19 for x86_64 and i386.

但根据 [jemalloc: opt.percpu_arena](http://jemalloc.net/jemalloc.3.html#opt.percpu_arena) 的说法，如果用户没有特别指定，jemalloc 不会绑核。[jemalloc TUNNING](https://github.com/jemalloc/jemalloc/blob/dev/TUNING.md) 建议用户只在线程迁移不频繁的时候才开启该选项。

在本篇文章中，我们假设 jemalloc 不绑核，因而在阅读源码的过程中可以忽略 `arena_s::last_thd` 等字段。

```c
#define TSD_INITIALIZER {                 \
    ATOMIC_INIT(tsd_state_uninitialized), \
    TCACHE_ENABLED_ZERO_INITIALIZER,      \
    false,                                \
    0,                                    \
    0,                                    \
    0,                                    \
    0,                                    \
    0,                                    \
    0,                                    \
    NULL,                                 \
    RTREE_CTX_ZERO_INITIALIZER,           \
    NULL,                                 \
    NULL,                                 \
    NULL,                                 \
    TSD_BINSHARDS_ZERO_INITIALIZER,       \
    TCACHE_ZERO_INITIALIZER,              \
    WITNESS_TSD_INITIALIZER               \
    MALLOC_TEST_TSD_INITIALIZER           \
}
// Global variables in tsd.c.
// defined(JEMALLOC_TLS)
JEMALLOC_TSD_TYPE_ATTR(tsd_t) tsd_tls = TSD_INITIALIZER;
pthread_key_t tsd_tsd;
bool tsd_booted = false;
```

```c
tsd_t *
tsd_fetch_slow(tsd_t *tsd, bool minimal) {
    tsd_state_set(tsd, tsd_state_nominal);
    tsd_slow_update(tsd);
    /* Trigger cleanup handler registration. */
    tsd_set(tsd);
    tsd_data_init(tsd);
}
```

```c
#define MALLOCX_ARENA_BITS 1
#define MALLOCX_ARENA_LIMIT ((1 << MALLOCX_ARENA_BITS) - 1)
atomic_p_t arenas[MALLOCX_ARENA_LIMIT];
```
