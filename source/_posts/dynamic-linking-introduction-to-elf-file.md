---
layout: post
title: "Dynamic Linking: Introduction To Elf File"
date: 2020-11-24 10:42:03
tags:
  - dynamic linking
---

# 导读

> “工欲善其事，必先利其器。”

本文会介绍 ELF 文件以及阅读 ELF 文件的工具，熟悉 ELF 文件对探索动态链接是很有好处的。

# 环境

```dockerfile
FROM debian:buster
LABEL maintainer="837940593@qq.com"

ENV DEBIAN_FRONTEND noninteractive
RUN apt-get update
RUN apt-get install -y build-essential bear make gcc g++ gdb

# Compile linker.
RUN mkdir /root/glibc
WORKDIR /root/glibc
RUN apt-get install -y wget
RUN apt-get install -y gawk bison texinfo gettext
RUN wget http://ftp.gnu.org/gnu/libc/glibc-2.28.tar.gz
RUN tar -xzvf glibc-2.28.tar.gz
RUN mkdir build
WORKDIR /root/glibc/build
RUN ../glibc-2.28/configure CFLAGS="-O1 -ggdb -w" --with-tls --enable-add-ons=nptl --prefix="$PWD/install"
RUN bear make -j8
RUN make install -j8

# Install tools.
# Install hexdump.
RUN apt-get install -y bsdmainutils
# Install lief.
RUN apt-get install -y python3 python3-pip
RUN pip3 install lief

CMD /bin/bash
```

```bash
# uname -r
4.19.76-linuxkit
# cat /etc/*-release | grep -E "VERSION_ID|ID"
VERSION_ID="10"
ID=debian
```

```bash
# gcc --version | head -n 1
gcc (Debian 8.3.0-6) 8.3.0
# ldd --version | head -n 1
ldd (Debian GLIBC 2.28-10) 2.28
```

# 一个小例子

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

# 了解 ELF 文件

## 工具概述

### Dump 二进制

```bash
# od --skip-bytes=0 --read-bytes=8 --format=xL main
# 64 bits
0000000 00010102464c457f
0000010
# od --skip-bytes=0 --read-bytes=8 --format=xI main
# 32 bits
0000000 464c457f 00010102
0000010
# od --skip-bytes=0 --read-bytes=8 --format=xS main
# 16 bits
0000000 457f 464c 0102 0001
0000010
# od --skip-bytes=0 --read-bytes=8 --format=xC main
# 8 bits
0000000 7f 45 4c 46 02 01 01 00
0000010
# od --skip-bytes=0 --read-bytes=8 --format=xC -c main
# 8 bits with characters
0000000  7f  45  4c  46  02  01  01  00
        177   E   L   F 002 001 001  \0
0000010
```

阅读字符串：

```bash
# dd if=libfoo.so of=libfoo.strtab ibs=1 obs=1 skip=$((0x3660)) count=$((0x15e))
350+0 records in
350+0 records out
350 bytes copied, 0.000862803 s, 406 kB/s
# strings libfoo.strtab | head -n 2
crtstuff.c
deregister_tm_clones
```

查找字符串：

```bash
# strings -t x libfoo.so | head -n 2
319 __gmon_start__
328 _ITM_deregisterTMCloneTable
```

`x` 表示用十六进制显示字符串的 offset 。

### Dump 汇编代码

```bash
# objdump -d libfoo.so --start-address=0x1020 --stop-address=$((0x1020+0x10))
0000000000001020 <.plt>:
    1020:   ff 35 e2 2f 00 00       pushq  0x2fe2(%rip)  # 4008 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:   ff 25 e4 2f 00 00       jmpq   *0x2fe4(%rip) # 4010 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:   0f 1f 40 00             nopl   0x0(%rax)
# objdump -d -j .text main | tail -n 2
00000000000011b0 <__libc_csu_fini>:
    11b0:       c3                      retq
# objdump -d --disassemble-zeroes -j .data main | tail -n 2
0000000000004028 <__dso_handle>:
    4028:       28 40 00 00 00 00 00 00                             (@......
```

### Dump 元信息

```bash
# readelf --file-header main
# readelf --program-headers main
# readelf --section-headers main
```

### 解析特定 sections

```bash
# readelf --dynamic main | head -n 5 | tail -n 4
Dynamic section at offset 0x2dd8 contains 28 entries:
  Tag        Type                         Name/Value
 0x0000000000000001 (NEEDED)             Shared library: [libfoo.so]
 0x0000000000000001 (NEEDED)             Shared library: [libc.so.6]
# readelf --symbols main | grep "Symbol" -A2
Symbol table '.dynsym' contains 7 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
--
Symbol table '.symtab' contains 69 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
# readelf --dyn-syms main | grep "Symbol" -A2
Symbol table '.dynsym' contains 7 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
# readelf --relocs main | grep "Relocation" -A2
Relocation section '.rela.dyn' at offset 0x4c8 contains 8 entries:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000003dc8  000000000008 R_X86_64_RELATIVE                    1130
--
Relocation section '.rela.plt' at offset 0x588 contains 1 entry:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000004018  000400000007 R_X86_64_JUMP_SLO 0000000000000000 _Z3foov + 0
# readelf -p .strtab main | head -n 5 | tail -n 4
String dump of section '.strtab':
  [     1]  crtstuff.c
  [     c]  deregister_tm_clones
  [    21]  __do_global_dtors_aux
```

## ELF 文件概述

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/ELF_Executable_and_Linkable_Format_diagram_by_Ange_Albertini.png)

File Header 和 Program Header 在 ELF 文件的开头，Section Header 在 ELF 文件的结尾。

接下来我们会用 readelf 直接查看元数据，也会用 od 以二进制方式看看每一个 Header 。

### File Header

```bash
# readelf --file-header main
ELF Header:
  Magic:   7f 45 4c 46 02 01 01 00 00 00 00 00 00 00 00 00
  Class:                             ELF64
  Data:                              2's complement, little endian
  Version:                           1 (current)
  OS/ABI:                            UNIX - System V
  ABI Version:                       0
  Type:                              DYN (Shared object file)
  Machine:                           Advanced Micro Devices X86-64
  Version:                           0x1
  Entry point address:               0x1050
  Start of program headers:          64 (bytes into file)
  Start of section headers:          14680 (bytes into file)
  Flags:                             0x0
  Size of this header:               64 (bytes)
  Size of program headers:           56 (bytes)
  Number of program headers:         11
  Size of section headers:           64 (bytes)
  Number of section headers:         30
  Section header string table index: 29
```

File Header 各个字段的含义可以参考[维基百科](https://en.wikipedia.org/wiki/Executable_and_Linkable_Format#File%20header) 。

> The ELF header is 52 or 64 bytes long for 32-bit and 64-bit binaries respectively.

```bash
# od --skip-bytes=0 --read-bytes=64 --format=xC main
```

| 位移（八进制） |          内容           |                             解释                             |
| :------------: | :---------------------: | :----------------------------------------------------------: |
|    0000000     |       7f 45 4c 46       |                     ELF (magic number).                      |
|                |           02            |           1 is 32-bit format, 2 is 64-bit format.            |
|                |           01            |         1 is big endianness, 2 is litte endianness.          |
|                |           01            |    Set to 1 for the original and current version of ELF.     |
|                |           00            |              ABI version, it is often set to 0.              |
|                |           00            |              Further specifies the ABI version.              |
|                |  00 00 00 00 00 00 00   |            Padding, should be filled with zeros.             |
|    0000020     |          03 00          |         Identifies object file type, 0x3 is ET_DYN.          |
|                |          3e 00          |    Specifies instruction set architecture, 0x3e is amd64.    |
|                |       01 00 00 00       |          Set to 1 for the original version of ELF.           |
|                | 50 10 00 00 00 00 00 00 |                     Entry point address.                     |
|    0000040     | 40 00 00 00 00 00 00 00 |      The start of the program header table. 0x40 = 64.       |
|                | 58 39 00 00 00 00 00 00 |            The start of the section header table.            |
|    0000060     |       00 00 00 00       |      Interpretation depends on the target architecture.      |
|                |          40 00          |                     Size of file header.                     |
|                |          38 00          |            Size of a program header table entry.             |
|                |          0b 00          |        Number of entries in the program header table.        |
|                |          40 00          |            Size of a section header table entry.             |
|                |          1e 00          |        Number of entries in the section header table.        |
|                |          1d 00          | Index of the section header table entry that contains the section names. |
|    0000100     |                         |                                                              |

File Header 帮助链接器：

1. 确认是否可以装载文件，包括系统是 32 位还是 64 位、大小端、ABI 版本等；
2. 决定如何装载文件，包括 Program Header 和 Section Header 的位置及大小、如何寻找 section 名称、entry point address 等。

### Program Header

```bash
# readelf --program-headers main
Program Headers:
  Type           Offset             VirtAddr           PhysAddr
                 FileSiz            MemSiz              Flags  Align
  PHDR           0x0000000000000040 0x0000000000000040 0x0000000000000040
                 0x0000000000000268 0x0000000000000268  R      0x8
  INTERP         0x00000000000002a8 0x00000000000002a8 0x00000000000002a8
                 0x0000000000000033 0x0000000000000033  R      0x1
      [Requesting program interpreter: /root/glibc/build/install/lib/ld-linux-x86-64.so.2]
  ...
```

```cpp
// /usr/include/elf.h
typedef uint32_t Elf64_Word;
typedef uint64_t Elf64_Xword;
typedef struct
{
  Elf64_Word    p_type;                 /* Segment type */
  Elf64_Word    p_flags;                /* Segment flags */
  Elf64_Off     p_offset;               /* Segment file offset */
  Elf64_Addr    p_vaddr;                /* Segment virtual address */
  Elf64_Addr    p_paddr;                /* Segment physical address */
  Elf64_Xword   p_filesz;               /* Segment size in file */
  Elf64_Xword   p_memsz;                /* Segment size in memory */
  Elf64_Xword   p_align;                /* Segment alignment */
} Elf64_Phdr;
```

```bash
# od --skip-bytes=$((0x40 + 0x38 * 1)) --read-bytes=0x38 --format=xL main
```

| 位移（八进制） |       内容       |           解释            |
| :------------: | :--------------: | :-----------------------: |
|    0000170     |     00000003     |         PT_INTERP         |
|                |     00000004     |      Segment flags.       |
|                | 00000000000002a8 |   Segment file offset.    |
|    0000210     | 00000000000002a8 | Segment virtual address.  |
|                | 00000000000002a8 | Segment physical address. |
|    0000230     | 0000000000000033 |   Segment size in file.   |
|                | 0000000000000033 |  Segment size in memory.  |
|    0000250     | 0000000000000001 |    Segment alignment.     |

比较让人迷惑的字段是 Segment physical address ，根据 [What is a section and why do we need it](https://stackoverflow.com/questions/16812574/elf-files-what-is-a-section-and-why-do-we-need-it) 和[写一个工具来了解ELF文件（二）](https://zhuanlan.zhihu.com/p/54399161) 两篇文章，Segment physical address 在现代操作系统中已经没有用处了，GCC 一般将其置为 Segment virtual address 。

```bash
# od --skip-bytes=0x2a8 --read-bytes=0x33 --format=xC -c main
0001250  2f  72  6f  6f  74  2f  67  6c  69  62  63  2f  62  75  69  6c
          /   r   o   o   t   /   g   l   i   b   c   /   b   u   i   l
0001270  64  2f  69  6e  73  74  61  6c  6c  2f  6c  69  62  2f  6c  64
          d   /   i   n   s   t   a   l   l   /   l   i   b   /   l   d
0001310  2d  6c  69  6e  75  78  2d  78  38  36  2d  36  34  2e  73  6f
          -   l   i   n   u   x   -   x   8   6   -   6   4   .   s   o
0001330  2e  32  00
          .   2  \0
0001333
```

根据 Program Header 的指导，从 0x2a8 开始连续读 0x33 个字节，就是 interpreter 在文件系统中的路径。

Program Header 最重要的作用是指导链接器如何装载 ELF 文件，要注意：由于对齐或者前面的某个 Segment 在文件中的大小和在内存中的大小不一致，Segment 在文件中的起始地址未必等于在内存中的起始地址，比如：

```bash
# readelf --program-headers main
  Type           Offset             VirtAddr           PhysAddr
                 FileSiz            MemSiz              Flags  Align
  ...
  LOAD           0x0000000000002dc8 0x0000000000003dc8 0x0000000000003dc8
                 0x0000000000000268 0x0000000000000270  RW     0x1000
```

LOAD Segment 在文件中的起始地址是 0x2dc8 ，在内存中的起始地址是 0x3dc8 ，两者并不相等。

### Section Header

```bash
# readelf --section-headers main
Section Headers:
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  ...
  [13] .plt.got          PROGBITS         0000000000001040  00001040
       0000000000000008  0000000000000008  AX       0     0     8
  ...
  [28] .strtab           STRTAB           0000000000000000  00003650
       00000000000001fa  0000000000000000           0     0     1
  ...
```

```cpp
typedef uint32_t Elf64_Word;
typedef uint64_t Elf64_Xword;
typedef struct
{
  Elf64_Word    sh_name;                /* Section name (string tbl index) */
  Elf64_Word    sh_type;                /* Section type */
  Elf64_Xword   sh_flags;               /* Section flags */
  Elf64_Addr    sh_addr;                /* Section virtual addr at execution */
  Elf64_Off     sh_offset;              /* Section file offset */
  Elf64_Xword   sh_size;                /* Section size in bytes */
  Elf64_Word    sh_link;                /* Link to another section */
  Elf64_Word    sh_info;                /* Additional section information */
  Elf64_Xword   sh_addralign;           /* Section alignment */
  Elf64_Xword   sh_entsize;             /* Entry size if section holds table */
} Elf64_Shdr;
```

```bash
# od --skip-bytes=$((0x3958 + 0x40 * 13)) --read-bytes=0x40 --format=xL main
```

| 位移（八进制） |       内容       |                    解释                    |
| :------------: | :--------------: | :----------------------------------------: |
|    0036230     |     00000094     |     Section name (string table index).     |
|                |     00000001     |        Section type, SHT_PROGBITS.         |
|                | 0000000000000006 | Section flags, SHF_ALLOC \| SHF_EXECINSTR. |
|    0036250     | 0000000000001040 |          Section virtual address.          |
|                | 0000000000001040 |            Section file offset.            |
|    0036270     | 0000000000000008 |           Section size in bytes.           |
|                |     00000000     |          Link to another section.          |
|                |     00000000     |      Additional section information.       |
|    0036310     | 0000000000000008 |             Section alignment.             |
|                | 0000000000000008 |     Entry size if section holds table.     |

根据 [man elf](https://man7.org/linux/man-pages/man5/elf.5.html) 的描述，sh_link / sh_info 的含义都取决于 section 。

## .plt & .got.plt / .plt.got & .got

Debug 技巧：先用 `info proc mappings` 获取 start address ，再用 `watch *(unsigned long long*)(<start_addr> + <addr>)` 就能看到改变特定地址的栈了。

1. .plt.got & .got 同 .plt & .got.plt 一样，都是一组用于重定位的 sections ；
2. 不同之处是：
    1. .plt.got & .got 没有 lazy binding ，由链接器直接触发重定位；
    2. .plt & .got.plt 有 lazy binding ，在第一次调用函数时触发重定位。

### .plt & .got.plt

```bash
# objdump -d -j .plt main
0000000000001020 <.plt>:
    1020:       ff 35 e2 2f 00 00       pushq  0x2fe2(%rip)        # 4008 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:       ff 25 e4 2f 00 00       jmpq   *0x2fe4(%rip)        # 4010 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:       0f 1f 40 00             nopl   0x0(%rax)

0000000000001030 <_Z3foov@plt>:
    1030:       ff 25 e2 2f 00 00       jmpq   *0x2fe2(%rip)        # 4018 <_Z3foov>
    1036:       68 00 00 00 00          pushq  $0x0
    103b:       e9 e0 ff ff ff          jmpq   1020 <.plt>
```

```bash
# readelf --section-headers main | grep -E "Nr|.got.plt" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [23] .got.plt          PROGBITS         0000000000004000  00003000
       0000000000000020  0000000000000008  WA       0     0     8
```

```bash
# od --skip-bytes=$((0x1036 + 0x2fe2 - 0x4000 + 0x3000)) --read-bytes=8 --format=xL main
0030030 0000000000001036
0030040
```

```bash
# readelf --relocs main | grep "$(printf '%x' $((0x1036 + 0x2fe2)))" -B2
Relocation section '.rela.plt' at offset 0x590 contains 1 entry:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000004018  000400000007 R_X86_64_JUMP_SLO 0000000000000000 _Z3foov + 0
```

.got.plt 表项（虚存地址是 0x1036 + 0x2fe2）会发生两次改变：

1. 从 0x1036 变成 start address + 0x1036 ：
    1. 由运行时链接器在 .rela.plt (R\_X86\_64\_JUMP\_SLOT) 表项的指导下完成，调用栈是 `dl_main -> _dl_relocate_object -> elf_dynamic_do_Rela` ；
    2. 是同文件重定位，仅仅加上了 start address ，不需要查找符号，执行速度快；
2. 从 start address + 0x1036 变成 `foo` 函数的首地址 ：
    1. 由用户代码在函数 `foo` 第一次被调用时触发，调用栈是 `main -> _dl_runtime_resolve_xsavec -> _dl_fixup` ；
    2. 是跨文件重定位，需要查找符号，执行速度慢。

### .plt.got & .got

```bash
# objdump -d -j .plt.got main
0000000000001040 <__cxa_finalize@plt>:
    1040:       ff 25 b2 2f 00 00       jmpq   *0x2fb2(%rip)        # 3ff8 <__cxa_finalize@GLIBC_2.2.5>
    1046:       66 90                   xchg   %ax,%ax
```

```bash
# readelf --section-headers main | grep -E "Nr| .got " -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [22] .got              PROGBITS         0000000000003fd8  00002fd8
       0000000000000028  0000000000000008  WA       0     0     8
```

```bash
# od --skip-bytes=$((0x1046 + 0x2fb2 - 0x3fd8 + 0x2fd8)) --read-bytes=8 --format=xL main
0027770 0000000000000000
0030000
```

```bash
# readelf --relocs main | grep -E "Offset|$(printf '%x' $((0x1046 + 0x2fb2)))"
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000003ff8  000600000006 R_X86_64_GLOB_DAT 0000000000000000 __cxa_finalize@GLIBC_2.2.5 + 0
```

.got 表项（虚存地址是 0x1046 + 0x2fb2）只会发生一次改变，从 0x0 变成 `__cxa_finalize` 函数的首地址：

1. 由运行时链接器在 .rela.dyn (R\_X86\_64\_GLOB\_DAT) 表项的指导下完成，调用栈是 `dl_main -> _dl_relocate_object -> elf_dynamic_do_Rela -> elf_machine_rela` ；
2. 是跨文件重定位，需要查找符号，执行速度慢。

## .rela.dyn & .rela.plt

以 foo.cpp 为例：

```cpp
// foo.cpp
#include <iostream>
namespace {
int var = 1;
void bar() { std::cout << "bar" << std::endl; }
}
void foo() {}
```

### .rela.dyn / .rela.plt

根据 [Linux Foundation Referenced Specifications: Additional Special Sections](https://refspecs.linuxfoundation.org/LSB_4.1.0/LSB-Core-S390/LSB-Core-S390/sections.html) 的说法：

1. .rela.plt section 负责配合 .plt section 完成[跨文件重定位](https://clcanny.github.io/2020/11/21/dynamic-linking-relocation-across-files/) ；
2. .rela.dyn 负责其它类型的重定位。

### .rela.dyn & .rela.plt 与 .symtab 的关系

.symtab 中的 undefined symbols 都能在 relocation sections 中找到：

```bash
# readelf --symbols --wide libfoo.so | grep ".symtab" -A 100 | grep "UND" | awk '{print $8}' | sort
__cxa_atexit@@GLIBC_2.2.5
__cxa_finalize@@GLIBC_2.2.5
__gmon_start__
_ITM_deregisterTMCloneTable
_ITM_registerTMCloneTable
_Jv_RegisterClasses
_ZNSolsEPFRSoS_E@@GLIBCXX_3.4
_ZNSt8ios_base4InitC1Ev@@GLIBCXX_3.4
_ZNSt8ios_base4InitD1Ev@@GLIBCXX_3.4
_ZSt4cout@@GLIBCXX_3.4
_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@@GLIBCXX_3.4
_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc@@GLIBCXX_3.4
```

```bash
# readelf --relocs --wide libfoo.so | grep -v "\<Offset\>" | awk '{print $5}' | sort | uniq
__cxa_atexit@GLIBC_2.2.5
__cxa_finalize@GLIBC_2.2.5
__gmon_start__
_ITM_deregisterTMCloneTable
_ITM_registerTMCloneTable
_Jv_RegisterClasses
offset
_ZNSolsEPFRSoS_E@GLIBCXX_3.4
_ZNSt8ios_base4InitC1Ev@GLIBCXX_3.4
_ZNSt8ios_base4InitD1Ev@GLIBCXX_3.4
_ZSt4cout@GLIBCXX_3.4
_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@GLIBCXX_3.4
_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc@GLIBCXX_3.4
```

# 参考资料

ELF (except .plt and .got.plt and etc.):

+ [Wikipedia: Executable and Linkable Format](https://en.wikipedia.org/wiki/Executable_and_Linkable_Format)
+ [Keith Makan: Introduction to the ELF Format (Part VII): Dynamic Linking / Loading and the .dynamic section](http://blog.k3170makan.com/2018/11/introduction-to-elf-format-part-vii.html)
+ [知乎：写一个工具来了解ELF文件（二）](https://zhuanlan.zhihu.com/p/54399161)
+ [Stack Overflow: What is a section and why do we need it](https://stackoverflow.com/questions/16812574/elf-files-what-is-a-section-and-why-do-we-need-it)
+ [Stack Overflow: Difference between Program header and Section Header in ELF](https://stackoverflow.com/questions/23379880/difference-between-program-header-and-section-header-in-elf)
+ [Oracle Solaris Blog: GNU Hash ELF Sections](https://blogs.oracle.com/solaris/gnu-hash-elf-sections-v2)
+ [ORACLE: Dynamic Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-42444.html)

.plt and .got.plt and etc.:

+ [Stack Exchange: What is PLT/GOT?](https://reverseengineering.stackexchange.com/questions/1992/what-is-plt-got)
+ [Stack Overflow: Why does the PLT exist in addition to the GOT, instead of just using the GOT?](https://stackoverflow.com/questions/43048932/why-does-the-plt-exist-in-addition-to-the-got-instead-of-just-using-the-got)
+ [Stack Overflow: .plt .plt.got what is different?](https://stackoverflow.com/questions/58076539/plt-plt-got-what-is-different)
+ [Stack Overflow: What is the difference between .got and .got.plt section?](https://stackoverflow.com/questions/11676472/what-is-the-difference-between-got-and-got-plt-section)
+ [Technovelty: PLT and GOT - the key to code sharing and dynamic libraries](https://www.technovelty.org/linux/plt-and-got-the-key-to-code-sharing-and-dynamic-libraries.html)
+ [System Overlord: GOT and PLT for pwning.](https://systemoverlord.com/2017/03/19/got-and-plt-for-pwning.html)
+ [LIEF: 05 - Infecting the plt/got](https://lief.quarkslab.com/doc/latest/tutorials/05_elf_infect_plt_got.html)

.rela.dyn and .rela.plt:

+ [Linux Foundation Referenced Specifications: Additional Special Sections](https://refspecs.linuxfoundation.org/LSB_4.1.0/LSB-Core-S390/LSB-Core-S390/sections.html)
+ [Keith Makan: Introduction to The ELF Format (Part VI): The Symbol Table and Relocations (Part 2)](http://blog.k3170makan.com/2018/10/introduction-to-elf-format-part-vi_18.html)
