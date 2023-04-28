---
layout: post
title: "Dynamic Linking: Merge Static String Table"
date: 2020-11-24 12:46:23
categories:
  - dynamic linking
---

```bash
od --skip-bytes=0x3650 --read-bytes=0x1fa --format=xC -c main
```

```bash
(gdb) bt
#0  LIEF::ELF::Section::size (this=0x555556133ff0, size=543) at /home/demons/LIEF/src/ELF/Section.cpp:237
#1  0x00005555556d1db6 in LIEF::ELF::Section::content(std::vector<unsigned char, std::allocator<unsigned char> >&&) (this=0x555556133ff0,
    content=<unknown type in /home/demons/extend-ststic-string-table/extend, CU 0x4260c8, DIE 0x4a2382>) at /home/demons/LIEF/src/ELF/Section.cpp:354
#2  0x00005555556e8532 in LIEF::ELF::Builder::build_static_symbols<LIEF::ELF::ELF64> (this=0x7fffffffe190) at /home/demons/LIEF/src/ELF/Builder.tcc:545
#3  0x00005555556dd146 in LIEF::ELF::Builder::build<LIEF::ELF::ELF64> (this=0x7fffffffe190) at /home/demons/LIEF/src/ELF/Builder.tcc:115
#4  0x00005555556db00d in LIEF::ELF::Builder::build (this=0x7fffffffe190) at /home/demons/LIEF/src/ELF/Builder.cpp:85
#5  0x00005555556019fc in LIEF::ELF::Binary::write (this=0x5555561322b0, filename="main-modified") at /home/demons/LIEF/src/ELF/Binary.cpp:1686
#6  0x00005555555ee540 in main () at extend.cpp:9
```

# 参考资料

+ [Stack Overflow: String table in ELF](https://stackoverflow.com/questions/11289843/string-table-in-elf)
