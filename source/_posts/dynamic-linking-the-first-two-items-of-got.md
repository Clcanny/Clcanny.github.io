---
layout: post
title: "Dynamic Linking The First Two Items Of GOT"
date: 2021-01-30 00:06:34
tags:
  - dynamic linking
---

# 导读

1. 本篇文章提及的 Global Offset Table 是 .got.plt section ，不是 .got section ，[Dynamic Linking: Introduction To Elf File](https://stackoverflow.com/questions/49812485/where-is-the-got0-global-offset-table-used) 介绍了两者的差异；
2. GOT[0] 是 dynamic section 的首地址，ld.so 自加载的过程会依赖于它；
3. GOT[1] 指向 `link_map` ；
4. GOT[2] 指向 `_dl_runtime_resolve_xsave` 。

# 环境 & 例子

本文使用的环境与 [Dynamic Linking: Introduction To Elf File](https://clcanny.github.io/2020/11/24/dynamic-linking-introduction-to-elf-file/#%E7%8E%AF%E5%A2%83) 使用的环境一致。

```cpp
// gcc -fPIC -ggdb -O0 -shared -Wl,--dynamic-linker=/root/glibc/build/install/lib/ld-linux-x86-64.so.2 foo.cpp -o libfoo.so
void foo() {}
```

```cpp
// gcc main.cpp -L$PWD -Wl,-rpath=$PWD -Wl,--dynamic-linker=/root/glibc/build/install/lib/ld-linux-x86-64.so.2 -lfoo -o main
extern void foo();
int main() {
    foo();
}
```

# GOT[0]

摘抄自 [Stack Overflow: Where is the GOT[0] (global offset table) used?](https://stackoverflow.com/questions/49812485/where-is-the-got0-global-offset-table) ：

> The tables first entry (number zero) is reserved to hold the address of the dynamic structure, referenced with the symbol \_DYNAMIC.

摘抄自 [System V Application Binary Interface (Version 1.0)](https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-1.0.pdf) ：

> This (GOT[0]) allows a program, such as the dynamic linker, to find its own dynamic structure without having yet processed its relocation entries. This is especially important for the dynamic linker, because it must initialize itself without relying on other programs to relocate its memory image.

## 有人访问 ld.so 的 GOT[0]

```bash
# readelf --section-headers /root/glibc/build/install/lib/ld-2.28.so | grep -E "Nr|.got.plt|.dynamic" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [17] .dynamic          DYNAMIC          0000000000026e78  00025e78
       0000000000000170  0000000000000010  WA       5     0     8
  [19] .got.plt          PROGBITS         0000000000027000  00026000
       0000000000000050  0000000000000008  WA       0     0     8
# od --skip-bytes=0x26000 --read-bytes=8 --format=xL /root/glibc/build/install/lib/ld-2.28.so
0460000 0000000000026e78
```

```bash
# (gdb) info proc mappings
0x7ffff7fd6000     0x7ffff7fd7000     0x1000        0x0 /root/glibc/build/install/lib/ld-2.28.so
# (gdb) rwatch *(unsigned long long*)(0x7ffff7fd6000 + 0x27000)
# (gdb) start
Hardware read watchpoint 1: *(unsigned long long*)(0x7ffff7fd6000 + 0x27000)
Value = 159352
# (gdb) bt
0x00007ffff7fd7e01 in _dl_start (arg=0x7fffffffed40) at ../sysdeps/x86_64/dl-machine.h:59
0x00007ffff7fd7098 in _start () from /root/glibc/build/install/lib/ld-linux-x86-64.so.2
```

```cpp
// /root/glibc/glibc-2.28/sysdeps/x86_64/dl-machine.h
// Return the link-time address of _DYNAMIC.  Conveniently, this is the
// first element of the GOT.  This must be inlined in a function which
// uses global data.
static inline ElfW(Addr) __attribute__((unused)) elf_machine_dynamic(void) {
    // This produces an IP-relative reloc which is resolved at link time.
    extern const ElfW(Addr) _GLOBAL_OFFSET_TABLE_[] attribute_hidden;
    return _GLOBAL_OFFSET_TABLE_[0];
}

// Return the run-time load address of the shared object.
static inline ElfW(Addr) __attribute__((unused))
elf_machine_load_address(void) {
    // Compute the difference between the runtime address of _DYNAMIC as seen
    // by an IP-relative reference, and the link-time address found in the
    // special unrelocated first GOT entry.
    extern ElfW(Dyn) _DYNAMIC[] attribute_hidden;
    return (ElfW(Addr)) & _DYNAMIC - elf_machine_dynamic();
}
```

# GOT[1]

GOT[1] 指向 `link_map` ，由运行时链接器负责填写：

# GOT[2]

GOT[2] 指向 `_dl_runtime_resolve_xsave` ，由运行时链接器负责填写：

# 参考资料

+ [Stack Overflow: Where is the GOT[0] (global offset table) used?](https://stackoverflow.com/questions/49812485/where-is-the-got0-global-offset-table-used)

+ [System V Application Binary Interface (Version 1.0)](https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-1.0.pdf)

+ [System V Application Binary Interface (Draft Version 0.90): Dynamic Linking](https://www.ucw.cz/~hubicka/papers/abi/node22.html)
