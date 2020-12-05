---
layout: post
title: "Dynamic Linking: Relocation Types"
date: 2020-12-03 01:47:10
tags:
  - dynamic linking
---

# 证明

```cpp
// foo.cpp
// g++ -std=c++11 foo.cpp -O0 -ggdb -shared -fPIC -o libfoo.so
#include <iostream>
int var = 1;
void foo() { std::cout << var << std::endl; }
```

```cpp
// main.cpp
// g++ main.cpp -O0 -ggdb -Wl,--dynamic-linker=/root/glibc/build/install/lib/ld-linux-x86-64.so.2 \
//     -L${PWD} -Wl,-rpath=${PWD} -lfoo                                                           \
//     -Wl,-rpath=/usr/lib/x86_64-linux-gnu                                                       \
//     -Wl,-rpath=/lib/x86_64-linux-gnu                                                           \
//     -o main
int main() {}
```

```bash
# readelf --relocs libfoo.so
Relocation section '.rela.dyn' at offset 0x580 contains 12 entries:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000003db8  000000000008 R_X86_64_RELATIVE                    1130
000000003dc0  000000000008 R_X86_64_RELATIVE                    11b4
000000003dc8  000000000008 R_X86_64_RELATIVE                    10f0
000000004038  000000000008 R_X86_64_RELATIVE                    4038
000000003fc0  000c00000006 R_X86_64_GLOB_DAT 0000000000004040 var + 0
000000003fc8  000100000006 R_X86_64_GLOB_DAT 0000000000000000 __cxa_finalize@GLIBC_2.2.5 + 0
000000003fd0  000200000006 R_X86_64_GLOB_DAT 0000000000000000 _ZSt4endlIcSt11char_tr@GLIBCXX_3.4 + 0
000000003fd8  000500000006 R_X86_64_GLOB_DAT 0000000000000000 _ZSt4cout@GLIBCXX_3.4 + 0
000000003fe0  000800000006 R_X86_64_GLOB_DAT 0000000000000000 _ITM_deregisterTMClone + 0
000000003fe8  000900000006 R_X86_64_GLOB_DAT 0000000000000000 __gmon_start__ + 0
000000003ff0  000a00000006 R_X86_64_GLOB_DAT 0000000000000000 _ITM_registerTMCloneTa + 0
000000003ff8  000b00000006 R_X86_64_GLOB_DAT 0000000000000000 _ZNSt8ios_base4InitD1E@GLIBCXX_3.4 + 0

Relocation section '.rela.plt' at offset 0x6a0 contains 4 entries:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000004018  000300000007 R_X86_64_JUMP_SLO 0000000000000000 __cxa_atexit@GLIBC_2.2.5 + 0
000000004020  000400000007 R_X86_64_JUMP_SLO 0000000000000000 _ZNSolsEPFRSoS_E@GLIBCXX_3.4 + 0
000000004028  000600000007 R_X86_64_JUMP_SLO 0000000000000000 _ZNSt8ios_base4InitC1E@GLIBCXX_3.4 + 0
000000004030  000700000007 R_X86_64_JUMP_SLO 0000000000000000 _ZNSolsEi@GLIBCXX_3.4 + 0
```

从 [United Computer Wizards: Relocation Types](https://www.ucw.cz/~hubicka/papers/abi/node19.html) 找到 AMD x86-64 relocation types ：

|          Name          | Value | Field  |           Calculation            |
|          :-:           |  :-:  |  :-:   |               :-:                |
|    R\_X86\_64\_NONE    |   0   |  none  |               none               |
|    R\_X86\_64\_COPY    |   5   |  none  |               none               |
| R\_X86\_64\_GLOB\_DAT  |   6   | word64 |                S                 |
| R\_X86\_64\_JUMP\_SLOT |   7   | word64 |                S                 |
|  R\_X86\_64\_RELATIVE  |   8   | word64 | BaseAddressAfterLoading + Addend |

## R\_X86\_64\_RELATIVE

```bash
# readelf --relocs libfoo.so
Relocation section '.rela.dyn' at offset 0x580 contains 12 entries:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000003db8  000000000008 R_X86_64_RELATIVE                    1130
000000003dc0  000000000008 R_X86_64_RELATIVE                    11b4
000000003dc8  000000000008 R_X86_64_RELATIVE                    10f0
000000004038  000000000008 R_X86_64_RELATIVE                    4038
```

```bash
# objdump -d -j .text libfoo.so | grep -E "(1130|11b4|10f0|4038).*>:" | sort
00000000000010f0 <__do_global_dtors_aux>:
0000000000001130 <frame_dummy>:
00000000000011b4 <_GLOBAL__sub_I_foo.cpp>:
```

```bash
(gdb) p/x 0x7ffff7fcb000 + 0x4038
$2 = 0x7ffff7fcf038
(gdb) x/a 0x7ffff7fcb000 + 0x4038
0x7ffff7fcf038: 0x7ffff7fcf038
```

.rela.dyn 指导运行时链接器：

1. 将 0x3db8 填上 `frame_dummy` 的首地址；
2. 将 0x3dc0 填上 `_GLOBAL__sub_I_foo.cpp` 的首地址；
3. 将 0x3dc8 填上 `__do_global_dtors_aux` 的首地址；
4. 将 0x4038 指向它自己。

## R\_X86\_64\_GLOB\_DAT

从 [Acronyms relevant to Executable and Linkable Format (ELF)](https://stevens.netmeister.org/631/elf.html) 摘抄了一段概述：

> So what about R\_X86\_64\_GLOB\_DAT relocation type in ld.so? First, `RESOLVE_MAP` (a macro defined within elf/dl-reloc.c) is called (with `r_type` = `R_X86_64_GLOB_DAT`) to find out which ELF binary (could be the user's program or its dependent dynamic libraries) contains this symbol. Then R\_X86\_64\_GLOB\_DAT relocation type is calculated as Base Address + Symbol Value + Addend where Base Address is the base address of ELF binary which contains the symbol, and Symbol Value is the symbol value from the symbol table of ELF binary which contains the symbol.

```c
// elf_machine_rela 内嵌在 _dl_relocate_object 内，因而可以使用定义于 _dl_relocate_object 作用域内的变量。
void elf_machine_rela(struct link_map* map,
                      const ElfW(Rela) * reloc,
                      const ElfW(Sym) * sym,
                      const struct r_found_version* version,
                      void* const reloc_addr_arg,
                      int skip_ifunc) {
  ElfW(Addr)* const reloc_addr = reloc_addr_arg;
  const unsigned long int r_type = ELFW(R_TYPE)(reloc->r_info);
  struct link_map* sym_map = RESOLVE_MAP(&sym, version, r_type);
  // The core function of `RESOLVE_MAP` macro is:
  // _dl_lookup_symbol_x(strtab + sym->st_name,
  //                     l,
  //                     &sym,
  //                     scope,
  //                     version,
  //                     elf_machine_type_class(r_type),
  //                     DL_LOOKUP_ADD_DEPENDENCY,
  //                     NULL);
  ElfW(Addr) value = SYMBOL_ADDRESS(sym_map, sym, true);
  // The core function of `SYMBOL_ADDRESS` macro is:
  // sym_map->l_addr + sym->st_value;
  switch (r_type) {
  case R_X86_64_GLOB_DAT:
  case R_X86_64_JUMP_SLOT:
    *reloc_addr = value + reloc->r_addend;
    break;
  }
}
```

## R\_X86\_64\_JUMP\_SLO

# Debug 技巧

通过以下步骤能迅速定位到执行重定位的函数：

1. 通过 `info proc mappings` 得到动态链接库在虚拟内存中的偏移量（通过 `info sharedlibrary` 得到的是 .text section 的地址）；
2. 通过 ` watch *(unsigned long long*)(<l_addr> + <offset>)` 得到改变值的函数栈。

```bash
(gdb) info proc mappings
          Start Addr           End Addr       Size     Offset objfile
      0x7ffff7fcb000     0x7ffff7fcc000     0x1000        0x0 /test/libfoo.so
```

```bash
(gdb) watch *(unsigned long long*)(0x7ffff7fcb000 + 0x4038)
Hardware watchpoint 2: *(unsigned long long*)(0x7ffff7fcb000 + 0x4038)
(gdb) start
Hardware watchpoint 2: *(unsigned long long*)(0x7ffff7fcb000 + 0x4038)
Old value = <unreadable>
New value = 140737353936952
0x00007ffff7fe159c in elf_machine_rela_relative (reloc_addr_arg=0x7ffff7fcf038, reloc=0x7ffff7fcb5c8, l_addr=140737353920512) at ../sysdeps/x86_64/dl-machine.h:539
539           *reloc_addr = l_addr + reloc->r_addend;
```

# 参考资料

+ [Acronyms relevant to Executable and Linkable Format (ELF)](https://stevens.netmeister.org/631/elf.html)
+ [United Computer Wizards: Relocation Types](https://www.ucw.cz/~hubicka/papers/abi/node19.html)
+ [Stack Exchange: Why does ldd and (gdb) info sharedlibrary show a different library base address?](https://reverseengineering.stackexchange.com/questions/6657/why-does-ldd-and-gdb-info-sharedlibrary-show-a-different-library-base-addr)
