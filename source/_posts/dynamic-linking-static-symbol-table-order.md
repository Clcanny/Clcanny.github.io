---
layout: post
title: dynamic-linking-static-symbol-table-order
date: 2020-11-21 13:10:08
tags:
  - dynamic linking
---

symtab_node::register_symbol // gcc/symtab.c

```bash
wget https://ftp.gnu.org/gnu/gcc/gcc-8.3.0/gcc-8.3.0.tar.gz
tar -xzvf gcc-8.3.0.tar.gz
cd gcc-8.3.0
./contrib/download_prerequisites
cd .. && mkdir gcc-8.3.0-build && cd gcc-8.3.0-build
CFLAGS="-O0 -ggdb" CXXFLAGS="-O0 -ggdb" $PWD/../gcc-8.3.0/configure --prefix=$PWD/install --enable-languages=c,c++,fortran,go --disable-multilib
make -j8
```

# 参考资料

+ [Linkers and Loaders](https://www.iecc.com/linker/)
+ [https://www.iecc.com/linker/](https://akkadia.org/drepper/dsohowto.pdf)
+ [GCC Wiki: Installing GCC](https://gcc.gnu.org/wiki/InstallingGCC)
