---
layout: post
title: "Dynamic Linking: Relocation Types"
date: 2020-12-03 01:47:10
tags:
  - dynamic linking
---

```cpp
// foo.cpp
// g++ -std=c++11 foo.cpp -O0 -ggdb -shared -fPIC -o libfoo.so
#include <iostream>
namespace {
int var = 1;
void bar() { std::cout << "bar" << std::endl; }
}
void foo() {}
```

```bash
# readelf --relocs --wide libfoo.so
Relocation section '.rela.dyn' at offset 0x608 contains 12 entries:
    Offset             Info             Type               Symbol's Value  Symbol's Name + Addend
0000000000200db0  0000000000000008 R_X86_64_RELATIVE                         8d0
0000000000200db8  0000000000000008 R_X86_64_RELATIVE                         982
0000000000200dc0  0000000000000008 R_X86_64_RELATIVE                         890
0000000000201038  0000000000000008 R_X86_64_RELATIVE                         201038
0000000000200fc0  0000000100000006 R_X86_64_GLOB_DAT      0000000000000000 __gmon_start__ + 0
0000000000200fc8  0000000200000006 R_X86_64_GLOB_DAT      0000000000000000 _Jv_RegisterClasses + 0
0000000000200fd0  0000000500000006 R_X86_64_GLOB_DAT      0000000000000000 _ZNSt8ios_base4InitD1Ev@GLIBCXX_3.4 + 0
0000000000200fd8  0000000600000006 R_X86_64_GLOB_DAT      0000000000000000 _ITM_deregisterTMCloneTable + 0
0000000000200fe0  0000000800000006 R_X86_64_GLOB_DAT      0000000000000000 _ITM_registerTMCloneTable + 0
0000000000200fe8  0000000900000006 R_X86_64_GLOB_DAT      0000000000000000 __cxa_finalize@GLIBC_2.2.5 + 0
0000000000200ff0  0000000a00000006 R_X86_64_GLOB_DAT      0000000000000000 _ZSt4cout@GLIBCXX_3.4 + 0
0000000000200ff8  0000000c00000006 R_X86_64_GLOB_DAT      0000000000000000 _ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@GLIBCXX_3.4 + 0

Relocation section '.rela.plt' at offset 0x728 contains 4 entries:
    Offset             Info             Type               Symbol's Value  Symbol's Name + Addend
0000000000201018  0000000300000007 R_X86_64_JUMP_SLOT     0000000000000000 _ZNSt8ios_base4InitC1Ev@GLIBCXX_3.4 + 0
0000000000201020  0000000400000007 R_X86_64_JUMP_SLOT     0000000000000000 __cxa_atexit@GLIBC_2.2.5 + 0
0000000000201028  0000000700000007 R_X86_64_JUMP_SLOT     0000000000000000 _ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc@GLIBCXX_3.4 + 0
0000000000201030  0000000b00000007 R_X86_64_JUMP_SLOT     0000000000000000 _ZNSolsEPFRSoS_E@GLIBCXX_3.4 + 0
```

# 参考资料

+ [Acronyms relevant to Executable and Linkable Format (ELF)](https://stevens.netmeister.org/631/elf.html)
