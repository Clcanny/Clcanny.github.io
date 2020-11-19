---
layout: post
title: "Dynamic linking: symbol search order"
date: 2020-11-18 13:50:23
tags:
  - Dynamic linkging
---

# Code

对于大多数链接过程，`link_map->l_scope[0]` 指向 `GL(dl_ns)[nsid]._ns_loaded->l_searchlist` ，又因为 `GL(dl_ns)[nsid]._ns_loaded` 是 `main_map` ，所以 `link_map->l_scope[0]` 指向 `main_map->l_searchlist` 。

```c
/* Storage management for the chain of loaded shared objects.
   Copyright (C) 1995-2018 Free Software Foundation, Inc.
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

// Add the new link_map `new` to the end of the namespace list.
void _dl_add_to_namespace_list(struct link_map* new, Lmid_t nsid) {
  _dl_debug_printf(
      "\nadding object %s to 0x%x as global scope with namespace id %u\n\n",
      strlen(new->l_name) == 0 ? "<empty libname>" : new->l_name,
      GL(dl_ns)[nsid]._ns_loaded,
      nsid);

  if (GL(dl_ns)[nsid]._ns_loaded != NULL) {
    struct link_map* l = GL(dl_ns)[nsid]._ns_loaded;
    while (l->l_next != NULL)
      l = l->l_next;
    new->l_prev = l;
    new->l_next = NULL;
    l->l_next = new;
  } else {
    GL(dl_ns)[nsid]._ns_loaded = new;
  }
  ++GL(dl_ns)[nsid]._ns_nloaded;
  new->l_serial = GL(dl_load_adds);
  ++GL(dl_load_adds);
}

struct link_map* _dl_new_object(char* realname,
                                const char* libname,
                                int type,
                                struct link_map* loader,
                                int mode,
                                Lmid_t nsid) {
  _dl_debug_printf("\ncreating object of %s with namespace id %u\n\n",
                   strlen(libname) == 0 ? "<empty libname>" : libname,
                   nsid);
  struct link_map* new = (struct link_map*)calloc(
      sizeof(*new) + audit_space + sizeof(struct link_map*) + sizeof(*newname) +
          libname_len,
      1);

  // Counter for the scopes we have to handle.
  int idx = 0;
  if (GL(dl_ns)[nsid]._ns_loaded != NULL) {
    // Add the global scope.
    new->l_scope[idx++] = &GL(dl_ns)[nsid]._ns_loaded->l_searchlist;
    _dl_debug_printf("\nassigning l_searchlist (0x%x) of 0x%x as global scope "
                     "to l_scope[%u] of object %s\n\n",
                     &GL(dl_ns)[nsid]._ns_loaded->l_searchlist,
                     GL(dl_ns)[nsid]._ns_loaded,
                     idx - 1,
                     strlen(libname) == 0 ? "<empty libname>" : libname);
  }

  new->l_local_scope[0] = &new->l_searchlist;
  return new;
}
```

# Namespace

namespace 是链接器提供的隔离机制，根据 [glic wiki: Linker Namespaces](https://sourceware.org/glibc/wiki/LinkerNamespaces) 的说法，namespace 一开始用于隔离：

1. 可执行文件及其加载的动态链接库
2. LD_AUDIT 及其加载的动态链接库

正常情况下，可执行文件及其加载的动态链接库都会被加载到 id 为 `LM_ID_BASE` = 0 的 namespace 下，它们之间不存在隔离。

```cpp
// main.cpp
int main() {
}
```

```cpp
// lib.cpp
```

```makefile
# Makefile
all :
    gcc lib.cpp -shared -fPIC -o liba.so
    gcc lib.cpp -shared -fPIC -L$(PWD) -Wl,-rpath=$(PWD) -la -o libb.so
    gcc lib.cpp -shared -fPIC -L$(PWD) -Wl,-rpath=$(PWD) -lb -o libe.so
    gcc main.cpp                                                                        \
            -Wl,--dynamic-linker=$(PWD)/../glibc/build/install/lib/ld-linux-x86-64.so.2 \
            -L$(PWD) -Wl,-rpath=$(PWD) -le                                              \
            -o main
    LD_DEBUG=all ./main 2>&1 | grep "creating object"
```

```bash
# make
LD_DEBUG=all ./main 2>&1 | grep "creating object"
      2313:     creating object of <empty libname> with namespace id 0
      2313:     creating object of <empty libname> with namespace id 0
      2313:     creating object of libe.so with namespace id 0
      2313:     creating object of libc.so.6 with namespace id 0
      2313:     creating object of libb.so with namespace id 0
      2313:     creating object of liba.so with namespace id 0
```

各个动态链接库都使用了 id 为 0 的 namespace 。

# Scope

```bash
# LD_DEBUG=all ./main 2>&1 | grep -E "creating main map |assigning"
      2390:     creating main map at: 0x57cde190
      2390:     assigning l_searchlist (0x57cde450) of 0x57cde190 as global scope to l_scope[0] of object <empty libname>
      2390:     assigning l_searchlist (0x57cde450) of 0x57cde190 as global scope to l_scope[0] of object libe.so
      2390:     assigning l_searchlist (0x57cde450) of 0x57cde190 as global scope to l_scope[0] of object libc.so.6
      2390:     assigning l_searchlist (0x57cde450) of 0x57cde190 as global scope to l_scope[0] of object libb.so
      2390:     assigning l_searchlist (0x57cde450) of 0x57cde190 as global scope to l_scope[0] of object liba.so
```

各个动态链接库都使用了可执行文件的 `l_searchlist` 作为 `l_scope[0]` 。

# Order

# 参考资料

+ [glic wiki: Linker Namespaces](https://sourceware.org/glibc/wiki/LinkerNamespaces)
+ [Oracle: Establishing a Namespace](https://docs.oracle.com/cd/E19120-01/open.solaris/819-0690/chapter6-1243/index.html)
