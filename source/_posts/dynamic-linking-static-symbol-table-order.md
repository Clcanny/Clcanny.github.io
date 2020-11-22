---
layout: post
title: dynamic-linking-static-symbol-table-order
date: 2020-11-21 13:10:08
tags:
  - dynamic linking
---

symtab_node::register_symbol // gcc/symtab.c

根据 [Orcale: Symbol Table Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-79797.html) 的说法：

> Conventionally, the symbol's name gives the name of the source file that is associated with the object file. A file symbol has STB_LOCAL binding and a section index of SHN_ABS. This symbol, if present, precedes the other STB_LOCAL symbols for the file.

```bash
wget https://ftp.gnu.org/gnu/gcc/gcc-8.3.0/gcc-8.3.0.tar.gz
tar -xzvf gcc-8.3.0.tar.gz
cd gcc-8.3.0
./contrib/download_prerequisites
cd .. && mkdir gcc-8.3.0-build && cd gcc-8.3.0-build
CFLAGS="-O0 -ggdb" CXXFLAGS="-O0 -ggdb" $PWD/../gcc-8.3.0/configure --prefix=$PWD/install --enable-languages=c,c++,fortran,go --disable-multilib
make -j8
```

```
cc1: internal compiler error: in register_symbol, at symtab.c:377
0xa51e3d symtab_node::register_symbol()                                                                                                                                              /home/demons/gcc/build/../gcc-8.3.0/gcc/symtab.c:377
0xa5db5f cgraph_node::create(tree_node*)                                                                                                                                             /home/demons/gcc/build/../gcc-8.3.0/gcc/cgraph.c:523
0xa5dc89 cgraph_node::get_create(tree_node*)                                                                                                                                         /home/demons/gcc/build/../gcc-8.3.0/gcc/cgraph.c:545
0xa6e63c cgraph_node::finalize_function(tree_node*, bool)                                                                                                                            /home/demons/gcc/build/../gcc-8.3.0/gcc/cgraphunit.c:438
0xf251c0 function_reader::create_function()                                                                                                                                          /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:520
0xf24de7 function_reader::parse_function()
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:425
0xf24d95 function_reader::handle_unknown_directive(file_location, char const*)
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:411
0x1cc03e0 md_reader::handle_file()
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-md.c:1158
0x1cc049a md_reader::handle_toplevel_file()
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-md.c:1180
0x1cc0595 md_reader::read_file(char const*)
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-md.c:1325
0xf27988 read_rtl_function_body(char const*)
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:1617
0xfe379e selftest::rtl_dump_test::rtl_dump_test(selftest::location const&, char*)
        /home/demons/gcc/build/../gcc-8.3.0/gcc/selftest-rtl.c:92
0xf28342 test_loading_dump_fragment_1
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:1739
0xf2defe selftest::read_rtl_function_c_tests()
        /home/demons/gcc/build/../gcc-8.3.0/gcc/read-rtl-function.c:2176
```

# 参考资料

+ [Linkers and Loaders](https://www.iecc.com/linker/)
+ [https://www.iecc.com/linker/](https://akkadia.org/drepper/dsohowto.pdf)
+ [GCC Wiki: Installing GCC](https://gcc.gnu.org/wiki/InstallingGCC)
+ [Orcale: Symbol Table Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-79797.html)
