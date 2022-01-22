---
layout: post
title: jemalloc-tls
date: 2022-01-22 23:53:07
tags:
---

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
