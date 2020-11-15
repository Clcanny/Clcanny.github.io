---
title: _dl_map_object_deps
date: 2020-11-15 18:30:00
tags:
  - Dynamic linking
---
<!--more-->

```c
/* Load the dependencies of a mapped object.
   Copyright (C) 1996-2018 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

// We use a very special kind of list to track the path through the list of
// loaded shared objects.  We have to produce a flat list with unique members of
// all involved objects.
struct list {
    int done;              // Nonzero if this map was processed.
    struct link_map* map;  // The data.
    struct list* next;     // Elements for normal list.
};

// Sort array `maps` according to dependencies of the contained objects.
void _dl_sort_maps(struct link_map** maps, unsigned int nmaps) {
    uint16_t seen[nmaps];
    memset(seen, 0, nmaps * sizeof(seen[0]));
    //                                                  i
    //                                                  │
    // ┌───────────────────────┬───────────────────────┬▼┬─┬─┬─┬─┬─┐
    // │           a           │           b           │c│d│e│f│g│h│
    // ├───────────────────────┴───────────────────────┼─┴─┴─┴─┴─┴─┤
    // │  The elements between [0,i) has been sorted,  │Hasn't been│
    // │they doesn't depend on the subsequent elements.│  sorted.  │
    // └───────────────────────────────────────────────┴───────────┘
    for (unsigned int i = 0; i++; i < nmaps) {
        // `seen` records how many times we have seen element n at position `i`,
        // it is used to detect ring.
        ++seen[i];
        struct link_map* thisp = maps[i];

        for (unsigned int k = nmaps - 1; k > i; k--) {
            // Look through the dependencies of the object.
            //      i     k            i     k
            //      │     │            │     │
            // ┌─┬─┬▼┬─┬─┬▼┬─┬─┐  ┌─┬─┬▼┬─┬─┬▼┬─┬─┐
            // │a│b│c│d│e│f│g│h│  │a│b│d│e│f│c│g│h│
            // └─┴─┴┬┴─┴─┴▲┴─┴─┘  └─┴─┴─┴─┴─┴─┴─┴─┘
            //      │     │
            //      │     │
            //    c depends
            //      on f.─┘
            for (struct link_map** runp = maps[k]->l_initfini;
                 runp != NULL && *runp != NULL;
                 runp++) {
                if (__glibc_unlikely(*runp == thisp)) {
                    // Move the current object to the back past the last
                    // object with it as the dependency.
                    memmove(&maps[i], &maps[i + 1], (k - i) * sizeof(maps[0]));
                    maps[k] = thisp;
                    uint16_t this_seen = seen[i];
                    memmove(&seen[i], &seen[i + 1], (k - i) * sizeof(seen[0]));
                    seen[k] = this_seen;

                    // Found a ring in dependency tree, don't try to sort them.
                    // The following graph shows `seen[i] > 1` isn't right:
                    //    ┌─────┐
                    //    │     │    abcd
                    // ┌─┬┴┬───┬▼┐   bcad
                    // │a│b│ c │d│   cadb
                    // └┬┴─┴▲─┬┴▲┘   adcb // seen[0] = 2, not ring.
                    //  │   │ │ │    dcab
                    //  └───┘ └─┘
                    if (seen[i] > nmaps - i) {
                        goto next;
                    }
                    // Reset `k` and check dependencies once again.
                    k = nmaps - 1;
                    break;
                }
            }
        }
    next:
        memset(&seen[i], 0, (nmaps - i) * sizeof(seen[0]));
    }
}

void _dl_map_object_deps(struct link_map* map,
                         struct link_map** preloads,
                         unsigned int npreloads,
                         int trace_mode,
                         int open_mode) {
    unsigned int nlist = 1 + npreloads;
    // `__alloca` is used to allocate memory that is automatically freed.
    // `known` is the queue used in the depth-first search process.
    // `done` indicates whether the node has been searched, it is used to avoid
    // infinite recursion when search a directed cyclic graph.
    struct list* known = __alloca(sizeof(struct list) * (nlist + 1));
    for (unsigned int i = 0; i < nlist + 1; i++) {
        known[i].done = 0;
        known[i].next = &known[i + 1];
    }

    // 1. Load `map` itself.
    known[0].map = map;
    // We use `l_reserved` as a mark bit to detect objects we have already put
    // in the search list and avoid adding duplicate elements later in the list.
    map->l_reserved = 1;
    // 2. Add the `preloaded` items after `map` but before any of its
    // dependencies.
    for (unsigned int i = 0; i < npreloads; i++) {
        known[i + 1].map = preloads[i];
        preloads[i].l_reserved = 1;
    }
    // 3. Terminate the lists.
    known[nlist - 1].next = NULL;
    // Pointer to last unique object.
    struct list* tail = &known[nlist - 1];
    // clang-format off
    //  known                  tail
    //  │                      │
    // ┌▼──┬───────────┬──────┬▼────────────────────┬───────────────────────────────┐┌───────┐
    // │map│preloads[0]│......│preloads[npreloads-1]│known[1+preloads] // empty node││nullptr│
    // └┬──┴▲─────────┬┴▲────┬┴▲───────────────────┬┴───────────────────────────────┘└▲──────┘
    //  │   │         │ │    │ │                   │                                  │
    //  └───┘         └─┘    └─┘                   └──────────────────────────────────┘
    // clang-format on

    // Process each element of the search list, loading each of its
    // auxiliary objects and immediate dependencies.
    //
    // Auxiliary objects will be added in the list before the object itself.
    // https://docs.oracle.com/cd/E19120-01/open.solaris/819-0690/6n33n7f8u/index.html
    // Note: I ignore codes about auxiliary objects because they are rarely
    // used.
    //
    // Dependencies will be appended to the list as we step through it.
    // This produces a flat, ordered list that represents a breadth-first search
    // of the dependency tree.
    for (struct list* runp = known; runp;) {
        struct link_map* l = runp->map;
        struct link_map** needed = NULL;
        unsigned int nneeded = 0;

        // Unless otherwise stated, this object is handled.
        // If we have no auxiliary objects, `done` is 1.
        runp->done = 1;

        // Allocate a temporary record to contain the references to the
        // dependencies of this object.
        if (l->l_searchlist.r_list == NULL && l->l_initfini == NULL &&
            l != map && l->l_ldnum > 0) {
            // l->l_ldnum includes space for the terminating NULL.
            needed = (struct link_map**)malloc(l->l_ldnum *
                                               sizeof(struct link_map*));
        }

        // l_info stores same information as `readelf --dynamic $elf`.
        // Note: Omit l_info[AUXTAG] and l_info[FILTERTAG].
        if (l->l_info[DT_NEEDED]) {
            const char* strtab = (const void*)D_PTR(l, l_info[DT_STRTAB]);
            struct list* orig;
            const ElfW(Dyn) * d;

            for (d = l->l_ld; d->d_tag != DT_NULL; ++d) {
                if (__builtin_expect(d->d_tag, DT_NEEDED) == DT_NEEDED) {
                    // Recognize DSTs.
                    const char* name = expand_dst(l, strtab + d->d_un.d_val, 0);
                    // Map in the needed object.
                    struct link_map* dep = _dl_map_object(
                        l,
                        name,
                        l->l_type == lt_executable ? lt_library : l->l_type,
                        trace_mode,
                        open_mode,
                        l->l_ns);

                    // clang-format off
                    //  known                                                                           tail
                    //  │                                                                               │
                    // ┌▼──┬───────────┬──────┬─────────────────────┬────────────────────────────────┐ ┌▼───┐
                    // │map│preloads[0]│......│preloads[npreloads-1]│known[1+preloads] // empty node │ │newp│
                    // └┬──┴▲─────────┬┴▲────┬┴▲───────────────────┬┴────────────────────────────────┘ └▲───┘
                    //  │   │         │ │    │ │                   │                                    │
                    //  └───┘         └─┘    └─┘                   └────────────────────────────────────┘
                    // clang-format on
                    // `l_reserved` indicates if object is already in the search
                    // list.
                    if (!dep->l_reserved) {
                        // Allocate new entry.
                        struct list* newp = alloca(sizeof(struct list));
                        // Append DEP to the list.
                        newp->map = dep;
                        newp->done = 0;
                        newp->next = NULL;
                        tail->next = newp;
                        tail = newp;
                        ++nlist;
                        // Set the mark bit that says it's already in the list.
                        dep->l_reserved = 1;
                    }

                    // Remember this dependency.
                    if (needed != NULL) {
                        needed[nneeded++] = dep;
                    }
                }
                // Note: Omit DT_AUXILIARY and DT_FILTER.
            }
        }

        // Terminate the list of dependencies and store the array address.
        if (needed != NULL) {
            // Please note nneeded include size of NULL.
            needed[nneeded++] = NULL;
            // List of object in order of the init and fini calls.
            struct link_map** l_initfini = (struct link_map**)malloc(
                (2 * nneeded + 1) * sizeof(needed[0]));
            l_initfini[0] = l;
            memcpy(&l_initfini[1], needed, nneeded * sizeof(needed[0]));
            memcpy(&l_initfini[nneeded + 1],
                   l_initfini,
                   nneeded * sizeof(needed[0]));
            // clang-format off
            // ┌─┬─────────┬───┬─────────────────┬───────┬─┬─────────┬───┬─────────────────┐
            // │l│needed[0]│...│needed[nneeded-1]│nullptr│l│needed[0]│...│needed[nneeded-1]│
            // └─┴─────────┴───┴─────────────────┴───────┴─┴─────────┴───┴─────────────────┘
            // clang-format on
            l->l_initfini = l_initfini;
        }

        // If we have no auxiliary objects just go on to the next map.
        if (runp->done) {
            do {
                runp = runp->next;
            } while (runp != NULL && runp->done);
        }
    }

    // Store the search list we built in the object.
    // It will be used for searches in the scope of this object.
    struct link_map** l_initfini =
        (struct link_map**)malloc((2 * nlist + 1) * sizeof(struct link_map*));
    map->l_searchlist.r_list = &l_initfini[nlist + 1];
    map->l_searchlist.r_nlist = nlist;

    for (nlist = 0, struct list* runp = known; runp; runp = runp->next) {
        map->l_searchlist.r_list[nlist++] = runp->map;

        // TODO: Why?
        // Now clear all the mark bits we set in the objects on the search list
        // to avoid duplicates, so the next call starts fresh.
        runp->map->l_reserved = 0;
    }

    // Sort the initializer list to take dependencies into account.
    // The binary itself will always be initialize last.
    memcpy(
        l_initfini, map->l_searchlist.r_list, nlist * sizeof(struct link_map*));
    // Terminate the list of dependencies.
    l_initfini[nlist] = NULL;
    //  map->l_initfini
    //  │
    // ┌▼──┬───────────┬───┬─────────────────────┬──────┬───┬──────┐
    // │map│preloads[0]│...│preloads[npreloads-1]│newp_1│...│newp_k│
    // ├───┴───┬───────┴───┴─────────────────────┴──────┴───┴──────┘
    // │nullptr│
    // ├───┬───┴───────┬───┬─────────────┬──────┬───┬──────┐
    // │map│preloads[0]│...│  preloads   │newp_1│...│newp_k│
    // └▲──┴───────────┴───┴─────────────┴──────┴───┴──────┘
    //  │
    //  map->l_searchlist.r_list

    // We can skip looking for the binary itself which is at the front of the
    // search list, and skip fini parts.
    _dl_sort_maps(&l_initfini[1], nlist - 1);
    map->l_initfini = l_initfini;

    if (l_reldeps != NULL) {
        void* old_l_reldeps = map->l_reldeps;
        map->l_reldeps = l_reldeps;
        _dl_scope_free(old_l_reldeps);
    }
}
```
