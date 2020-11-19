---
layout: post
title: "Dynamic Linking: Symbol Search Order"
date: 2020-11-18 13:50:23
tags:
  - Dynamic linkging
---

# 导读

这篇文章探讨了**目前**链接器在各个文件之间查找符号的顺序，对于大多数链接过程：

1. 可执行文件及其加载的动态链接库都会被加载到 id 为 `LM_ID_BASE` = 0 的 namespace 下；
2. 符号都能在 `l_scope[0]` 指向的已加载文件列表（即 global scope ）中找到；
3. 查找符号的顺序是 `main_map->l_searchlist` 的顺序，也即广度优先遍历依赖树的顺序：
    1. `link_map->l_scope[0]` 指向 `GL(dl_ns)[nsid]._ns_loaded->l_searchlist` ，又因为 `GL(dl_ns)[nsid]._ns_loaded` 是 `main_map` ，所以 `link_map->l_scope[0]` 指向 `main_map->l_searchlist` ；
    2. 根据[上一篇文章](https://clcanny.github.io/2020/11/15/dynamic-linking-init-order/)的说法，`main_map->l_searchlist` 指向 `main_map->l_initfini` 的后半段，这部分未经 `_dl_sort_maps` 函数排序，仍然保持着广度优先遍历依赖树的顺序。

# Code

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

# 证明

## Namespace

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

## Scope

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

## Order

```cpp
// main.cpp
void sayHello();
int main() {
  sayHello();
}
```

```cpp
// b.cpp
#include <iostream>
extern const char* var;
void sayHello() {
  std::cout << var << std::endl;
}
```

```cpp
// f.cpp
const char* var = "I'm in f.";
```

```cpp
// g.cpp
const char* var = "I'm in g.";
```

```cpp
// empty.cpp
```

```makefile
# Makefile
all :
    g++ -std=c++11 empty.cpp -shared -fPIC -o libe.so
    g++ -std=c++11 f.cpp -shared -fPIC -o libf.so
    g++ -std=c++11 g.cpp -shared -fPIC -o libg.so
    g++ -std=c++11 empty.cpp -shared -fPIC -o libh.so
    g++ -std=c++11 empty.cpp -shared -fPIC -L$(PWD) -Wl,-rpath=$(PWD) -le -lf -o liba.so
    g++ -std=c++11 b.cpp -shared -fPIC -L$(PWD) -Wl,-rpath=$(PWD) -lg -lh -o libb.so
    g++ -std=c++11 -L$(PWD) -Wl,-rpath=$(PWD) -la -lb main.cpp -o main
    LD_DEBUG=all ./main 2>&1 | grep -E "var|I'm in"
```

```bash
# make
LD_DEBUG=all ./main 2>&1 | grep -E "var|I'm in"
      6382:     symbol=var;  lookup in file=./main [0]
      6382:     symbol=var;  lookup in file=/home/demons/_dl_map_objects_validate/search_symbol_order/liba.so [0]
      6382:     symbol=var;  lookup in file=/home/demons/_dl_map_objects_validate/search_symbol_order/libb.so [0]
      6382:     symbol=var;  lookup in file=/usr/lib/x86_64-linux-gnu/libstdc++.so.6 [0]
      6382:     symbol=var;  lookup in file=/lib/x86_64-linux-gnu/libm.so.6 [0]
      6382:     symbol=var;  lookup in file=/lib/x86_64-linux-gnu/libgcc_s.so.1 [0]
      6382:     symbol=var;  lookup in file=/lib/x86_64-linux-gnu/libc.so.6 [0]
      6382:     symbol=var;  lookup in file=/home/demons/_dl_map_objects_validate/search_symbol_order/libe.so [0]
      6382:     symbol=var;  lookup in file=/home/demons/_dl_map_objects_validate/search_symbol_order/libf.so [0]
      6382:     binding file /home/demons/_dl_map_objects_validate/search_symbol_order/libb.so [0] to /home/demons/_dl_map_objects_validate/search_symbol_order/libf.so [0]: normal symbol `var'
I'm in f.
```

# A coredump

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-symbol-search-order/coredump.png)

```cpp
// main.cpp
int main() {
}
```

```cpp
// a.cpp
#include <iostream>
#include <string>

namespace {
const std::string var = "I'm in a.";
}

void accessVar() {
  std::cout << var[0] << std::endl;
}
```

```cpp
// b.cpp
void accessVar();

struct AccessVar {
  AccessVar() {
    accessVar();
  }
} _;
```

```cpp
// e.cpp
#include <iostream>
#include <string>

namespace {
const std::string var = "I'm in e.";
}

void accessVar() {
  std::cout << var[0] << std::endl;
}
```

```makefile
# Makefile
all :
    g++ e.cpp -shared -fPIC -O3 -o libe.so
    g++ a.cpp -shared -fPIC -O3 -o liba.so
    g++ b.cpp -shared -fPIC -L$(PWD) -Wl,-rpath=$(PWD) -le -O3 -o libb.so
    g++ main.cpp -L$(PWD) -Wl,-rpath=$(PWD) -la -lb -O3 -o main
    LD_DEBUG=all ./main 2>&1 | grep -E "calling init|accessVar"
```

```bash
Segmentation fault
     14934:     calling init: /lib/x86_64-linux-gnu/libc.so.6
     14934:     calling init: /lib/x86_64-linux-gnu/libm.so.6
     14934:     calling init: /lib/x86_64-linux-gnu/libgcc_s.so.1
     14934:     calling init: /usr/lib/x86_64-linux-gnu/libstdc++.so.6
     14934:     calling init: /home/demons/_dl_map_objects_validate/search_symbol_order/libe.so
     14934:     calling init: /home/demons/_dl_map_objects_validate/search_symbol_order/libb.so
     14934:     symbol=_Z9accessVarv;  lookup in file=./main [0]
     14934:     symbol=_Z9accessVarv;  lookup in file=/home/demons/_dl_map_objects_validate/search_symbol_order/liba.so [0]
     14934:     binding file /home/demons/_dl_map_objects_validate/search_symbol_order/libb.so [0] to /home/demons/_dl_map_objects_validate/search_symbol_order/liba.so [0]: normal symbol `_Z9accessVarv'
```

初始化的顺序是 eba ，查找符号的顺序是 abe ，因此初始化 libb.so 的时候用到了来自 liba.so 的、尚未初始化的 `var` 变量，导致 coredump 。

# More

关于 Namespace 和 Scope 的 corner case ，后续会另写一篇文章来探讨。

# 参考资料

+ [glic wiki: Linker Namespaces](https://sourceware.org/glibc/wiki/LinkerNamespaces)
+ [Oracle: Establishing a Namespace](https://docs.oracle.com/cd/E19120-01/open.solaris/819-0690/chapter6-1243/index.html)
