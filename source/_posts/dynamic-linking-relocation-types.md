---
layout: post
title: "Dynamic Linking: Relocation Types"
date: 2020-12-03 01:47:10
tags:
  - dynamic linking
---

```bash
Hardware watchpoint 3: *(unsigned long long*)0x7ffff7fcedb8

Old value = <unreadable>
New value = 140737353924912
0x00007ffff7fe159c in elf_machine_rela_relative (reloc_addr_arg=0x7ffff7fcedb8, reloc=0x7ffff7fcb580, l_addr=140737353920512) at ../sysdeps/x86_64/dl-machine.h:539
539           *reloc_addr = l_addr + reloc->r_addend;
(gdb) bt
#0  0x00007ffff7fe159c in elf_machine_rela_relative (reloc_addr_arg=0x7ffff7fcedb8, reloc=0x7ffff7fcb580, l_addr=140737353920512) at ../sysdeps/x86_64/dl-machine.h:539
#1  elf_dynamic_do_Rela (skip_ifunc=<optimized out>, lazy=0, nrelative=<optimized out>, relsize=288, reladdr=<optimized out>, map=0x7ffff7fd0010) at do-rel.h:112
#2  _dl_relocate_object (scope=0x7ffff7fd0370, reloc_mode=<optimized out>, consider_profiling=consider_profiling@entry=0) at dl-reloc.c:258
#3  0x00007ffff7fdb57d in dl_main (phdr=<optimized out>, phnum=<optimized out>, user_entry=<optimized out>, auxv=<optimized out>) at rtld.c:2197
#4  0x00007ffff7fed268 in _dl_sysdep_start (start_argptr=start_argptr@entry=0x7fffffffed40, dl_main=dl_main@entry=0x7ffff7fd8439 <dl_main>) at ../elf/dl-sysdep.c:253
#5  0x00007ffff7fd8080 in _dl_start_final (arg=0x7fffffffed40) at rtld.c:415
#6  _dl_start (arg=0x7fffffffed40) at rtld.c:522
#7  0x00007ffff7fd7098 in _start () from /root/glibc/build/install/lib/ld-linux-x86-64.so.2
#8  0x0000000000000001 in ?? ()
#9  0x00007fffffffef06 in ?? ()
#10 0x0000000000000000 in ?? ()
```

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
objdump -d -j .text libfoo.so | grep -E "(1130|11b4|10f0|4038).*>:" | sort
00000000000010f0 <__do_global_dtors_aux>:
0000000000001130 <frame_dummy>:
00000000000011b4 <_GLOBAL__sub_I_foo.cpp>:
```

# 参考资料

+ [Acronyms relevant to Executable and Linkable Format (ELF)](https://stevens.netmeister.org/631/elf.html)
+ [United Computer Wizards: Relocation Types](https://www.ucw.cz/~hubicka/papers/abi/node19.html)
