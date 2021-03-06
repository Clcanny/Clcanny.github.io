---
layout: post
title: "Dynamic Linking The First Three Items Of GOT"
date: 2021-01-30 00:06:34
tags:
  - dynamic linking
---

# 导读

1. 本篇文章提及的 Global Offset Table 是 .got.plt section ，不是 .got section ，[Dynamic Linking: Introduction To Elf File](https://stackoverflow.com/questions/49812485/where-is-the-got0-global-offset-table-used) 介绍了两者的差异；
2. GOT[0] 是 .dynamic section 的首地址，ld.so 自加载的过程会依赖于它；
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

## 无人访问其它 ELF 文件的 GOT[0]

```bash
# readelf --section-headers main | grep -E "Nr|.got.plt|.dynamic" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [21] .dynamic          DYNAMIC          0000000000003dd8  00002dd8
       0000000000000200  0000000000000010  WA       6     0     8
  [23] .got.plt          PROGBITS         0000000000004000  00003000
       0000000000000020  0000000000000008  WA       0     0     8
# od --skip-bytes=0x3000 --read-bytes=8 --format=xL main
0030000 0000000000003dd8
```

```bash
# (gdb) info proc mappings
0x555555554000     0x555555555000     0x1000        0x0 /root/main
# (gdb) rwatch *(unsigned long long*)(0x555555554000 + 0x4000)
# (gdb) start
Temporary breakpoint 3, 0x0000555555555139 in main ()
```

# GOT[1] & GOT[2]

```bash
# readelf --section-headers main | grep -E "Nr|.got.plt" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [23] .got.plt          PROGBITS         0000000000004000  00003000
       0000000000000020  0000000000000008  WA       0     0     8
```

```bash
# (gdb) watch *(unsigned long long*)(0x555555554000 + 0x4000 + 0x8)
# (gdb) start
Hardware watchpoint 1: *(unsigned long long*)(0x555555554000 + 0x4000 + 0x8)
Old value = 0
New value = 140737354129808
# (gdb) bt
elf_machine_runtime_setup (profile=0, lazy=1, l=0x7ffff7ffe190) at ../sysdeps/x86_64/dl-machine.h:100
_dl_relocate_object (scope=0x7ffff7ffe4f0, reloc_mode=<optimized out>, consider_profiling=consider_profiling@entry=0) at dl-reloc.c:258
0x00007ffff7fdb57d in dl_main (phdr=<optimized out>, phnum=<optimized out>, user_entry=<optimized out>, auxv=<optimized out>) at rtld.c:2197
```

```cpp
static inline int __attribute__((unused, always_inline))
elf_machine_runtime_setup(struct link_map* l, int lazy, int profile) {
    if (l->l_info[DT_JMPREL] && lazy) {
        // The GOT entries for functions in the PLT have not yet been filled
        // in.  Their initial contents will arrange when called to push an
        // offset into the .rel.plt section, push _GLOBAL_OFFSET_TABLE_[1],
        // and then jump to _GLOBAL_OFFSET_TABLE_[2].
        Elf64_Addr* got = (Elf64_Addr*)D_PTR(l, l_info[DT_PLTGOT]);

        // Identify this shared object.
        *(ElfW(Addr)*)(got + 1) = (ElfW(Addr))l;

        // The got[2] entry contains the address of a function which gets
        // called to get the address of a so far unresolved function and
        // jump to it.  The profiling extension of the dynamic linker allows
        // to intercept the calls to collect information.  In this case we
        // don't store the address in the GOT so that all future calls also
        // end in this function.
        //
        // This function will get called to fix up the GOT entry
        // indicated by the offset on the stack, and then jump to
        // the resolved address.
        *(ElfW(Addr)*)(got + 2) = (ElfW(Addr)) & _dl_runtime_resolve_xsavec;
    }
    return lazy;
}
```

GOT[1] 指向 `link_map` ，GOT[2] 指向 `_dl_runtime_resolve_xsavec` ，它们由 `elf_machine_runtime_setup` 函数负责填写。

# 如何合并 ELF 文件？

1. .got.plt section 的前三项不要参与合并；
2. .plt section 的跳转位置需要修正；
3. .rela.plt section 的 `r_offset` 字段需要修正。

# 参考资料

+ [Stack Overflow: Where is the GOT[0] (global offset table) used?](https://stackoverflow.com/questions/49812485/where-is-the-got0-global-offset-table-used)
+ [System V Application Binary Interface (Version 1.0)](https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-1.0.pdf)
+ [System V Application Binary Interface (Draft Version 0.90): Dynamic Linking](https://www.ucw.cz/~hubicka/papers/abi/node22.html)