---
layout: post
title: "Dynamic Linking: Merge Static Symbol Table"
date: 2020-11-21 13:10:08
tags:
  - dynamic linking
---

# 导读

1. 来自某个文件的 LOCAL 符号都跟在代表该文件的 entry 之后；
3. 全局符号（ GLOBAL / WEAK ）排在本地符号（ LOCAL ）之后；
2. .symtab section header 的 information 是第一个全局符号在 .symtab section 的 index 。

根据 [Orcale: Symbol Table Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-79797.html) 的说法：

> Conventionally, the symbol's name gives the name of the source file that is associated with the object file. A file symbol has STB\_LOCAL binding and a section index of SHN\_ABS. This symbol, if present, precedes the other STB\_LOCAL symbols for the file.

# 证明

```cpp
// foo.cpp
// g++ foo.cpp -shared -fPIC -O0 -ggdb -o libfoo.so

namespace {
int bar = 1;
const char* name = "foo.cpp";
}  // anonymous namespace

void foo() {
}
```

```bash
# readelf --section-headers libfoo.so | grep -E "Nr|symtab" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [30] .symtab           SYMTAB           0000000000000000  00001270
       00000000000005d0  0000000000000018          31    51     8
```

```bash
# readelf --symbols libfoo.so
    30: 0000000000000000     0 FILE    LOCAL  DEFAULT  ABS crtstuff.c
    31: 0000000000200e10     0 OBJECT  LOCAL  DEFAULT   18 __JCR_LIST__
    32: 0000000000000570     0 FUNC    LOCAL  DEFAULT   11 deregister_tm_clones
    33: 00000000000005b0     0 FUNC    LOCAL  DEFAULT   11 register_tm_clones
    34: 0000000000000600     0 FUNC    LOCAL  DEFAULT   11 __do_global_dtors_aux
    35: 0000000000201030     1 OBJECT  LOCAL  DEFAULT   23 completed.6972
    36: 0000000000200e08     0 OBJECT  LOCAL  DEFAULT   17 __do_global_dtors_aux_fin
    37: 0000000000000640     0 FUNC    LOCAL  DEFAULT   11 frame_dummy
    38: 0000000000200e00     0 OBJECT  LOCAL  DEFAULT   16 __frame_dummy_init_array_

    39: 0000000000000000     0 FILE    LOCAL  DEFAULT  ABS foo.cpp
    40: 0000000000201020     4 OBJECT  LOCAL  DEFAULT   22 _ZN12_GLOBAL__N_13barE
    41: 0000000000201028     8 OBJECT  LOCAL  DEFAULT   22 _ZN12_GLOBAL__N_14nameE

    42: 0000000000000000     0 FILE    LOCAL  DEFAULT  ABS crtstuff.c
    43: 0000000000000728     0 OBJECT  LOCAL  DEFAULT   15 __FRAME_END__
    44: 0000000000200e10     0 OBJECT  LOCAL  DEFAULT   18 __JCR_END__

    45: 0000000000000000     0 FILE    LOCAL  DEFAULT  ABS
    46: 000000000000068c     0 NOTYPE  LOCAL  DEFAULT   14 __GNU_EH_FRAME_HDR
    47: 0000000000201000     0 OBJECT  LOCAL  DEFAULT   21 _GLOBAL_OFFSET_TABLE_
    48: 0000000000201030     0 OBJECT  LOCAL  DEFAULT   22 __TMC_END__
    49: 0000000000201018     0 OBJECT  LOCAL  DEFAULT   22 __dso_handle
    50: 0000000000200e18     0 OBJECT  LOCAL  DEFAULT   19 _DYNAMIC

    51: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND __gmon_start__
```

# 合并静态符号表

# 参考资料

+ [Linkers and Loaders](https://www.iecc.com/linker/)
+ [https://www.iecc.com/linker/](https://akkadia.org/drepper/dsohowto.pdf)
+ [Orcale: Symbol Table Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-79797.html)
