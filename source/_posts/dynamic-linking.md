---
title: Dynamic linking
date: 2020-10-07 00:28:00
tags:
  - dynamic linking
---
<!--more-->

# 导读

下文出现的 objects 均指代动态链接库和可执行文件。

本篇文章详细地介绍了 objects 重定位的过程：

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/guide.png)

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

### Dump 汇编代码

```bash
# objdump -d libfoo.so --start-address=0x1020 --stop-address=$((0x1020+0x10))
0000000000001020 <.plt>:
    1020:   ff 35 e2 2f 00 00       pushq  0x2fe2(%rip)  # 4008 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:   ff 25 e4 2f 00 00       jmpq   *0x2fe4(%rip) # 4010 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:   0f 1f 40 00             nopl   0x0(%rax)
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

## .got .plt .got.plt .plt.got

# 同文件重定位

## R_X86_64_IRELATIVE

```cpp
// test_x86_64_irelative.cpp
// gcc test_x86_64_irelative.cpp -O0 -ggdb -o test_x86_64_irelative
int global_var = 0xABCDEF12;
int* p_global_var = &global_var;
int main() {
}
```

```bash
# readelf --relocs test_x86_64_irelative
Relocation section '.rela.dyn' at offset 0x470 contains 9 entries:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000003e18  000000000008 R_X86_64_RELATIVE                    1120
000000003e20  000000000008 R_X86_64_RELATIVE                    10e0
000000004020  000000000008 R_X86_64_RELATIVE                    4020
000000004030  000000000008 R_X86_64_RELATIVE                    4028
000000003fd8  000100000006 R_X86_64_GLOB_DAT 0000000000000000 _ITM_deregisterTMClone + 0
000000003fe0  000200000006 R_X86_64_GLOB_DAT 0000000000000000 __libc_start_main@GLIBC_2.2.5 + 0
000000003fe8  000300000006 R_X86_64_GLOB_DAT 0000000000000000 __gmon_start__ + 0
000000003ff0  000400000006 R_X86_64_GLOB_DAT 0000000000000000 _ITM_registerTMCloneTa + 0
000000003ff8  000500000006 R_X86_64_GLOB_DAT 0000000000000000 __cxa_finalize@GLIBC_2.2.5 + 0
```

```bash
# readelf --section-headers test_x86_64_irelative | grep -E "Nr|\.data" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [23] .data             PROGBITS         0000000000004018  00003018
       0000000000000020  0000000000000000  WA       0     0     8
```

```bash
# od --skip-bytes=$((0x4028 - 0x4018 + 0x3018)) --read-bytes=4 --format=xI test_x86_64_irelative
0030060 abcdef12
# od --skip-bytes=$((0x4030 - 0x4018 + 0x3018)) --read-bytes=8 --format=xL test_x86_64_irelative
0030050 0000000000004028
```

0x4028 是 `global_var` 的地址，0x4030 是 `p_global_var` 的地址。

```cpp
auto inline void
__attribute ((always_inline))
elf_machine_rela_relative (ElfW(Addr) l_addr, const ElfW(Rela) *reloc,
                           void *const reloc_addr_arg)
{
  ElfW(Addr) *const reloc_addr = reloc_addr_arg;
    {
      assert (ELFW(R_TYPE) (reloc->r_info) == R_X86_64_RELATIVE);
      *reloc_addr = l_addr + reloc->r_addend;
    }
}
```

重定位公式：`*reloc_addr = l_addr + reloc->r_addend` ，`r_addend` 是 0x4028 ，也就是 `global_var` 的地址。

## R_X86_64_JUMP_SLOT

```bash
# readelf --relocs main | grep "R_X86_64_JUMP_SLO" -B2
Relocation section '.rela.plt' at offset 0x578 contains 1 entry:
  Offset          Info           Type           Sym. Value    Sym. Name + Addend
000000004018  000400000007 R_X86_64_JUMP_SLO 0000000000000000 _Z3foov + 0
```

```bash
# objdump -s -j .got.plt main | tail -n 3
Contents of section .got.plt:
 4000 d83d0000 00000000 00000000 00000000  .=..............
 4010 00000000 00000000 36100000 00000000  ........6.......
```

`R_X86_64_JUMP_SLOT` 标记的是 .got.plt 表项，.got.plt 表项也需要一次同文件重定位。

```cpp
auto inline void
__attribute ((always_inline))
elf_machine_lazy_rel (struct link_map *map,
                      ElfW(Addr) l_addr, const ElfW(Rela) *reloc,
                      int skip_ifunc)
{
  ElfW(Addr) *const reloc_addr = (void *) (l_addr + reloc->r_offset);
  const unsigned long int r_type = ELFW(R_TYPE) (reloc->r_info);

  /* Check for unexpected PLT reloc type.  */
  if (__glibc_likely (r_type == R_X86_64_JUMP_SLOT))
    {
      /* Prelink has been deprecated.  */
      if (__glibc_likely (map->l_mach.plt == 0))
        *reloc_addr += l_addr;
      else
        *reloc_addr =
          map->l_mach.plt
          + (((ElfW(Addr)) reloc_addr) - map->l_mach.gotplt) * 2;
    }
  // ...
```

重定位公式：`*reloc_addr += l_addr` 。

## Others

从 [Executable and Linkable Format 101 Part 3: Relocations](https://www.intezer.com/blog/elf/executable-and-linkable-format-101-part-3-relocations/) 中摘抄得到 x86_64 的重定位类型：

- A: Addend of Elfxx_Rela entries.
- B: Image base where the shared object was loaded in process virtual address space.
- G: Offset to the GOT relative to the address of the correspondent relocation entry’s symbol.
- GOT: Address of the Global Offset Table.
- L: Section offset or address of the procedure linkage table (PLT, .got.plt).
- P: The section offset or address of the storage unit being relocated.
  retrieved via r_offset relocation entry’s field.
- S: Relocation entry’s correspondent symbol value.
- Z: Size of Relocations entry’s symbol.

| Name               | Value | Field | Calculation                                 |
| :----------------- | :---- | :---- | :------------------------------------------ |
| R_X86_64_NONE      | 0     | None  | None                                        |
| R_X86_64_64        | 1     | qword | S + A                                       |
| R_X86_64_PC32      | 2     | dword | S + A – P                                   |
| R_X86_64_GOT32     | 3     | dword | G + A                                       |
| R_X86_64_PLT32     | 4     | dword | L + A – P                                   |
| R_X86_64_COPY      | 5     | None  | Value is copied directly from shared object |
| R_X86_64_GLOB_DAT  | 6     | qword | S                                           |
| R_X86_64_JUMP_SLOT | 7     | qword | S                                           |
| R_X86_64_RELATIVE  | 8     | qword | B + A                                       |
| R_X86_64_GOTPCREL  | 9     | dword | G + GOT + A – P                             |
| R_X86_64_32        | 10    | dword | S + A                                       |
| R_X86_64_32S       | 11    | dword | S + A                                       |
| R_X86_64_16        | 12    | word  | S + A                                       |
| R_X86_64_PC16      | 13    | word  | S + A – P                                   |
| R_X86_64_8         | 14    | word8 | S + A                                       |
| R_X86_64_PC8       | 15    | word8 | S + A – P                                   |
| R_X86_64_PC64      | 24    | qword | S + A – P                                   |
| R_X86_64_GOTOFF64  | 25    | qword | S + A – GOT                                 |
| R_X86_64_GOTPC32   | 26    | dword | GOT + A – P                                 |
| R_X86_64_SIZE32    | 32    | dword | Z + A                                       |
| R_X86_64_SIZE64    | 33    | qword | Z + A                                       |

## 如何阅读代码？

`_dl_relocate_object` 大量使用 `#ifdef` 语句和宏定义，导致很难阅读。因而需要用 bear 生成的 compile_commands.json 来还原编译命令，并加上 `-E -P` 选项，得到预处理之后的文件。

```bash
# pwd
/root/glibc/glibc-2.28/elf
# gcc -c -std=gnu11 -fgnu89-inline -O1 -Wall -Werror -Wundef -Wwrite-strings -fmerge-all-constants -fno-stack-protector -frounding-math -ggdb -w -Wstrict-prototypes -Wold-style-definition -fno-math-errno -fPIC -fno-stack-protector -DSTACK_PROTECTOR_LEVEL=0 -mno-mmx -ftls-model=initial-exec -I../include -I/root/glibc/build/elf -I/root/glibc/build -I../sysdeps/unix/sysv/linux/x86_64/64 -I../sysdeps/unix/sysv/linux/x86_64 -I../sysdeps/unix/sysv/linux/x86/include -I../sysdeps/unix/sysv/linux/x86 -I../sysdeps/x86/nptl -I../sysdeps/unix/sysv/linux/wordsize-64 -I../sysdeps/x86_64/nptl -I../sysdeps/unix/sysv/linux/include -I../sysdeps/unix/sysv/linux -I../sysdeps/nptl -I../sysdeps/pthread -I../sysdeps/gnu -I../sysdeps/unix/inet -I../sysdeps/unix/sysv -I../sysdeps/unix/x86_64 -I../sysdeps/unix -I../sysdeps/posix -I../sysdeps/x86_64/64 -I../sysdeps/x86_64/fpu/multiarch -I../sysdeps/x86_64/fpu -I../sysdeps/x86/fpu/include -I../sysdeps/x86/fpu -I../sysdeps/x86_64/multiarch -I../sysdeps/x86_64 -I../sysdeps/x86 -I../sysdeps/ieee754/float128 -I../sysdeps/ieee754/ldbl-96/include -I../sysdeps/ieee754/ldbl-96 -I../sysdeps/ieee754/dbl-64/wordsize-64 -I../sysdeps/ieee754/dbl-64 -I../sysdeps/ieee754/flt-32 -I../sysdeps/wordsize-64 -I../sysdeps/ieee754 -I../sysdeps/generic -I.. -I../libio -I. -D_LIBC_REENTRANT -include /root/glibc/build/libc-modules.h -DMODULE_NAME=rtld -include ../include/libc-symbols.h -DPIC -DSHARED -DTOP_NAMESPACE=glibc -E -P dl-reloc.c > dl-reloc.i
```

# 跨文件重定位

## 开始重定位：.plt .got.plt

.plt 和 .got.plt 配合完成 lazy binding ，图片摘抄自 [](https://lief.quarkslab.com/doc/latest/tutorials/05_elf_infect_plt_got.html) ：

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/plt-got-mechanism-first-time-call.jpg)

*With lazy binding, the first time that the function is called the* `got` *entry redirects to the plt instruction.*

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/plt-got-mechanism-second-time-call.jpg)

*The Second time,* `got` *entry holds the address in the shared library.*

以 main 调用 foo 为例：

```assembly
# objdump -d -j .text main
0000000000001135 <main>:
    1135:   55                      push   %rbp
    1136:   48 89 e5                mov    %rsp,%rbp
    1139:   e8 f2 fe ff ff          callq  1030 <_Z3foov@plt>
```

```assembly
# objdump -d -j .plt main
0000000000001020 <.plt>:
    1020:   ff 35 e2 2f 00 00       pushq  0x2fe2(%rip) # 4008 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:   ff 25 e4 2f 00 00       jmpq   *0x2fe4(%rip) # 4010 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:   0f 1f 40 00             nopl   0x0(%rax)

0000000000001030 <_Z3foov@plt>:
    1030:   ff 25 e2 2f 00 00       jmpq   *0x2fe2(%rip) # 4018 <_Z3foov>
    1036:   68 00 00 00 00          pushq  $0x0
    103b:   e9 e0 ff ff ff          jmpq   1020 <.plt>
```

rip + 0x2fe2 是重定位实现 lazy binding 留下的一个占位符，这个占位符的初始值指向 plt 的第二条指令（1036），第一次调用发生后，它会被链接器修改成 foo 函数的地址，从而完成重定位。

```bash
# readelf --section-headers main | grep -E "Nr|.got.plt" -A1
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
--
  [23] .got.plt          PROGBITS         0000000000004000  00003000
       0000000000000020  0000000000000008  WA       0     0     8
```

```bash
# od --skip-bytes=$((0x1036 + 0x2fe2 - 0x4000 + 0x3000)) --read-bytes=8 --format=xL main
0030030 0000000000001036
0030040
```

0x1020 是所有 plt 程序共用的部分，rip + 0x2fe2 指向 link_map ，rip + 0x2fe4 指向 `_dl_runtime_resolve_xsave` ，这两个地址都由链接器负责填写。

```bash
# od --skip-bytes=$((0x1026 + 0x2fe2 - 0x4000 + 0x3000)) --read-bytes=8 --format=xL main
0030010 0000000000000000
0030020
# od --skip-bytes=$((0x102c + 0x2fe4 - 0x4000 + 0x3000)) --read-bytes=8 --format=xL main
0030020 0000000000000000
0030030
```

剩下两个未解之谜：

1. link_map 是怎么构造出来的？
2. `_dl_runtime_resolve_xsave` 做了些什么？

## \_dl\_runtime\_resolve\_xsave: before \_dl\_fixup

`_dl_runtime_resolve_xsave` 定义于 /root/glibc/glibc-2.28/sysdeps/x86_64/dl-trampoline.h ，不过文件内大量使用 `#if` 语句，并不适合直接阅读。

\_dl\_runtime\_resolve\_xsave 在调用 \_dl\_fixup 之前的主要工作是：保存寄存器。

## \_dl\_fixup

`_dl_runtime_resolve_xsave` 的核心是位于 elf/dl-runtime.c 的 `_dl_fixup` ，`_dl_fixup` 的执行过程如下：

1. 用 `link_map` 访问 .dynamic ，分别取出 .rela.plt / .dynsym / .dynstr 的地址；

2. .rela.plt + 参数 `reloc_arg` ，求出当前函数的重定位表项 Elf64_Rela 的指针，记作 reloc ；

3. 以 `ELFW(R_SYM) (reloc->r_info)` 作为 .dynsym 的下标，求出当前函数的符号表项 `Elf64_Sym` 的指针，记作 `sym` ；

4. `.dynstr + sym->st_name` 得出符号名字 ；

5. 在动态链接库中查找这个函数的地址，并且把地址赋值给 `*(reloc->r_offset)` ，即 .got.plt 表项 。


### 访问 .dynamic 表项

```cpp
typedef struct
{
  Elf64_Sxword  d_tag;                  /* Dynamic entry type */
  union
    {
      Elf64_Xword d_val;                /* Integer value */
      Elf64_Addr d_ptr;                 /* Address value */
    } d_un;
} Elf64_Dyn;
```

```cpp
struct link_map
  {
    /* These first few members are part of the protocol with the debugger.
       This is the same format used in SVR4.  */

    ElfW(Addr) l_addr;          /* Difference between the address in the ELF
                                   file and the addresses in memory.  */
    char *l_name;               /* Absolute file name object was found in.  */
    ElfW(Dyn) *l_ld;            /* Dynamic section of the shared object.  */
    struct link_map *l_next, *l_prev; /* Chain of loaded objects.  */
    // ...
    /* Indexed pointers to dynamic section. */
    ElfW(Dyn) *l_info[DT_NUM + DT_THISPROCNUM + DT_VERSIONTAGNUM
                      + DT_EXTRANUM + DT_VALNUM + DT_ADDRNUM];
    // ...
  };
```

```cpp
// D_PTR 的两个定义用于：完成重定位之后和完成重定位之前，区别在于有没有加上 difference 。
/* All references to the value of l_info[DT_PLTGOT],
  l_info[DT_STRTAB], l_info[DT_SYMTAB], l_info[DT_RELA],
  l_info[DT_REL], l_info[DT_JMPREL], and l_info[VERSYMIDX (DT_VERSYM)]
  have to be accessed via the D_PTR macro.  The macro is needed since for
  most architectures the entry is already relocated - but for some not
  and we need to relocate at access time.  */
#ifdef DL_RO_DYN_SECTION
# define D_PTR(map, i) ((map)->i->d_un.d_ptr + (map)->l_addr)
#else
# define D_PTR(map, i) (map)->i->d_un.d_ptr
#endif
```

```bash
# readelf --dynamic main | head -n 8 | tail -n 6
  Tag        Type                         Name/Value
 0x0000000000000001 (NEEDED)             Shared library: [libfoo.so]
 0x0000000000000001 (NEEDED)             Shared library: [libc.so.6]
 0x000000000000001d (RUNPATH)            Library runpath: [/root/test]
 0x000000000000000c (INIT)               0x1000
 0x000000000000000d (FINI)               0x11b4
```

### 对比 .dynamic 与 section headers

初次接触 ELF 文件会被 .dynamic 和 section headers 的区别坑到，我们不禁想问：既然有 section headers 指明每个 sections 的起始地址，为什么还需要 .dynamic ？

```bash
# readelf --section-headers main | grep -E "Nr|.symtab" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [27] .symtab           SYMTAB           0000000000000000  00003050
       0000000000000600  0000000000000018          28    45     8
```

```bash
# readelf --dynamic main | grep -E "Tag|SYMTAB"
  Tag        Type                         Name/Value
 0x0000000000000006 (SYMTAB)             0x348
```

Section header 说 .symtab 的起始地址是 0x3050 ，.dynamic 表说 .symtab 的起始地址是 0x348 ，两者为什么会不一致？

```bash
# readelf --section-headers main | grep -E "Nr|348" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 5] .dynsym           DYNSYM           0000000000000348  00000348
       00000000000000a8  0000000000000018   A       6     1     8
```

事实上，0x348 是 .dynsym 的起始地址，即 .dynamic 表和 section headers 都使用了 symtab 这个名字，但两者完全不是一个意思。

同样的情况也发生在 strtab 上：

```bash
# readelf --section-headers main | grep -E "Nr|.strtab" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [28] .strtab           STRTAB           0000000000000000  00003650
       00000000000001fa  0000000000000000           0     0     1
  [29] .shstrtab         STRTAB           0000000000000000  0000384a
       0000000000000107  0000000000000000           0     0     1
```

```bash
# readelf --dynamic main | grep -E "Tag|STRTAB"
  Tag        Type                         Name/Value
 0x0000000000000005 (STRTAB)             0x3f0
```

```bash
# readelf --section-headers main | grep -E "Nr|3f0" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 6] .dynstr           STRTAB           00000000000003f0  000003f0
       000000000000009a  0000000000000000   A       0     0     1
```

.dynamic 表和 section headers 都使用了 strtab 这个名字，但两者完全不是一个意思。

### 访问 .rela.plt 表项

```cpp
// reloc_offset = reloc_arg ，是 _dl_fixup 的第二个参数。
const PLTREL *const reloc
  = (const void *) (D_PTR (l, l_info[DT_JMPREL]) + reloc_offset);
```

```cpp
/* Relocation table entry with addend (in section of type SHT_RELA).  */
typedef struct
{
  Elf64_Addr    r_offset;               /* Address */
  Elf64_Xword   r_info;                 /* Relocation type and symbol index */
  Elf64_Sxword  r_addend;               /* Addend */
} Elf64_Rela;
```

```bash
# readelf --dynamic main | grep -E "Tag|JMPREL"
  Tag        Type                         Name/Value
 0x0000000000000017 (JMPREL)             0x578
```

```bash
# readelf --section-headers main | grep -E "Nr|578" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [10] .rela.plt         RELA             0000000000000578  00000578
       0000000000000018  0000000000000018  AI       5    23     8
```

```bash
# export reloc_table_start_addr=0x578
# export reloc_entry_size=0x18
# export reloc_offset=0
# od --skip-bytes=$(($reloc_table_start_addr + $reloc_entry_size * $reloc_offset)) --read-bytes=$reloc_entry_size --format=xL main
0002570 0000000000004018 0000000400000007
0002610 0000000000000000
```

对照 `Elf64_Rela` 的定义，`r_info` 的值是 0x4 << 32 + 0x7 。

### 访问 .dynsym 表项

```cpp
/* We use this macro to refer to ELF macros independent of the native
   wordsize.  `ELFW(R_TYPE)' is used in place of `ELF32_R_TYPE' or
   `ELF64_R_TYPE'.  */
#define ELFW(type)      _ElfW (ELF, __ELF_NATIVE_CLASS, type)
#define ELF64_R_SYM(i)          ((i) >> 32)

const ElfW(Sym) *const symtab
  = (const void *) D_PTR (l, l_info[DT_SYMTAB]);
const ElfW(Sym) *sym = &symtab[ELFW(R_SYM) (reloc->r_info)];
```

所以 `ELFW(R_SYM) (reloc->r_info) == 4` 。

```cpp
typedef uint32_t Elf64_Word;
typedef uint64_t Elf64_Xword;
typedef uint16_t Elf64_Section;
typedef struct
{
  Elf64_Word    st_name;                /* Symbol name (string tbl index) */
  unsigned char st_info;                /* Symbol type and binding */
  unsigned char st_other;               /* Symbol visibility */
  Elf64_Section st_shndx;               /* Section index */
  Elf64_Addr    st_value;               /* Symbol value */
  Elf64_Xword   st_size;                /* Symbol size */
} Elf64_Sym;
```

```bash
# readelf --dynamic main | grep -E "Tag|SYMTAB"
  Tag        Type                         Name/Value
 0x0000000000000006 (SYMTAB)             0x348
```

```bash
# readelf --section-headers main | grep -E "Nr|348" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 5] .dynsym           DYNSYM           0000000000000348  00000348
       00000000000000a8  0000000000000018   A       6     1     8
```

```bash
# export symbol_table_start_addr=0x348
# export symbol_table_entry_size=0x18
# export symbol_table_entry_index=0x4
# od --skip-bytes=$(($symbol_table_start_addr + $symbol_table_entry_size * $symbol_table_entry_index)) --read-bytes=$symbol_table_entry_size --format=xL main
0001650 0000001200000050 0000000000000000
0001670 0000000000000000
```

对照 `Elf64_Sym` 的定义，`st_name` 的值是 0x50 。

### 访问 .dynstr 表项

```cpp
const char *strtab = (const void *) D_PTR (l, l_info[DT_STRTAB]);
result = _dl_lookup_symbol_x (strtab + sym->st_name, l, &sym, l->l_scope,
                              version, ELF_RTYPE_CLASS_PLT, flags, NULL);
```

```bash
# readelf --dynamic main | grep -E "Tag|STRTAB"
  Tag        Type                         Name/Value
 0x0000000000000005 (STRTAB)             0x3f0
```

```bash
# readelf --section-headers main | grep -E "Nr|3f0" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 6] .dynstr           STRTAB           00000000000003f0  000003f0
       000000000000009a  0000000000000000   A       0     0     1
```

```bash
# export string_table_start_addr=0x3f0
# export st_name=0x50
# od --skip-bytes=$(($string_table_start_addr + $st_name)) --read-bytes=0x8 --format=xC -c main
0002100  5f  5a  33  66  6f  6f  76  00
          _   Z   3   f   o   o   v  \0
```

函数 `foo` 在 mangle 后的名字是 `_Z3fooV` 。

### 查找符号

```cpp
// elf/dl-lookup.c
_dl_lookup_symbol_x
  do_lookup_x
```

`_dl_lookup_symbol_x` 遍历 `l->l_scope` ，对于每一个 `scope` 调用 `do_lookup_x` 函数寻找符号。

1. `l_scope` 和已加载的动态链接库的关系是什么？是怎么被构造出来的？
2. 如何在某个动态链接库内查找符号？

#### l_scope

##### l_scope 是什么？

```cpp
/* Structure to describe a single list of scope elements.  The lookup
   functions get passed an array of pointers to such structures.  */
struct r_scope_elem
{
  /* Array of maps for the scope.  */
  struct link_map **r_list;
  /* Number of entries in the scope.  */
  unsigned int r_nlist;
};

struct link_map
  {
    // ...
    /* Size of array allocated for 'l_scope'.  */
    size_t l_scope_max;
    /* This is an array defining the lookup scope for this link map.
       There are initially at most three different scope lists.  */
    struct r_scope_elem **l_scope;
    // ...
  };
```

摘抄自 [ld.so Scopes](http://log.or.cz/?p=129) ：

> The scope describes which libraries should be searched for symbol lookups occuring within the scope owner. (By the way, given that lookup scope may differ by caller, implementing `dlsym()` is not *that* trivial.) It is further divided into **scope elements (struct r_scope_elem)** – a single scope element basically describes a single search list of libraries, and the scope (**link_map.l_scope** is the scope used for symbol lookup) is list of such scope elements.

> To reiterate, a symbol lookup scope is a list of lists! Then, when looking up a symbol, the linker walks the lists in the order they are listed in the scope. But what really are the scope elements? There are two usual kinds:
>
> - The "global scope" – all libraries (ahem, link_maps) that have been requested to be loaded by the main program (what ldd on the binary file of the main program would print out, plus dlopen()ed stuff).
> - The "local scope" – DT_NEEDED library dependencies of the current link_map (what ldd on the binary file of the library would print out, plus dlopen()ed stuff).

> The global scope is shared between all link_maps (in the current namespace), while the local scope is owned by a particular library.

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/l_scope.jpeg)

##### 构造 l_scope

```cpp
// 以下代码只展示了有关于 l_scope 的部分
/* Allocate a `struct link_map' for a new object being loaded,
   and enter it into the _dl_loaded list.  */
struct link_map *
_dl_new_object (char *realname, const char *libname, int type,
                struct link_map *loader, int mode, Lmid_t nsid)
{
  struct link_map *new = (struct link_map *) calloc (sizeof (*new) + audit_space
                                    + sizeof (struct link_map *)
                                    + sizeof (*newname) + libname_len, 1);
  /* Use the 'l_scope_mem' array by default for the 'l_scope'
     information.  If we need more entries we will allocate a large
     array dynamically.  */
  new->l_scope = new->l_scope_mem;
  new->l_scope_max = sizeof (new->l_scope_mem) / sizeof (new->l_scope_mem[0]);
  /* Counter for the scopes we have to handle.  */
  int idx = 0;
  /* Insert the scope if it isn't the global scope we already added.  */
  if (idx == 0 || &loader->l_searchlist != new->l_scope[0])
  {
    if ((mode & RTLD_DEEPBIND) != 0 && idx != 0)
    {
      new->l_scope[1] = new->l_scope[0];
      idx = 0;
    }
    new->l_scope[idx] = &loader->l_searchlist;
  }
}
```

```cpp
// elf/rtld.c
// dl_main
_dl_add_to_namespace_list (main_map, LM_ID_BASE);
assert (main_map == GL(dl_ns)[LM_ID_BASE]._ns_loaded);
```

这里只探讨用得最多的 global scope ：

1. 加载文件时，代表 objects 的 `link_map` 会通过 `_dl_add_to_namespace_list` 函数添加到一个全局链表；
2. `dl_new_object` 会将 global scope 赋值给 `l_scope[0]` 。

#### \_dl\_setup\_hash

.gnu.hash 需要有多个导出符号才能较方便地分析，因此我们将使用 test_gnu_hash.cpp 作为待分析的文件：

```cpp
// test_gnu_hash.cpp
// g++ -std=c++11 -shared -fPIC test_gnu_hash.cpp -o libtest_gnu_hash.so
void foo() {}
void bar() {}
void test() {}
void haha() {}
void more() {}
```

编译器会准备好查找符号需要的数据，主要是布隆过滤器和哈希表。

```cpp
struct link_map
  {
    // ...
    /* Symbol hash table.  */
    // The number of hash buckets.
    Elf_Symndx l_nbuckets;
    // bitmask_words is the number of __ELF_NATIVE_CLASS sized words
    // in the Bloom filter portion of the hash table section. This value
    // must be non-zero, and must be a power of 2.
    // l_gnu_bitmask_idxbits = bitmask_nwords - 1
    Elf32_Word l_gnu_bitmask_idxbits;
    // A shift count used by the Bloom filter.
    // HashValue_2 = HashValue_1 >> l_gnu_shift.
    Elf32_Word l_gnu_shift;
    const ElfW(Addr) *l_gnu_bitmask;
    union
    {
      const Elf32_Word *l_gnu_buckets;
      const Elf_Symndx *l_chain;
    };
    union
    {
      const Elf32_Word *l_gnu_chain_zero;
      const Elf_Symndx *l_buckets;
    };
    // ...
  };
```

```cpp
void
_dl_setup_hash (struct link_map *map)
{
  if (__glibc_likely (map->l_info[ADDRIDX (DT_GNU_HASH)] != NULL))
    {
      Elf32_Word *hash32
        = (void *) D_PTR (map, l_info[ADDRIDX (DT_GNU_HASH)]);
      map->l_nbuckets = *hash32++;
      Elf32_Word symbias = *hash32++;
      Elf32_Word bitmask_nwords = *hash32++;
      /* Must be a power of two.  */
      assert ((bitmask_nwords & (bitmask_nwords - 1)) == 0);
      map->l_gnu_bitmask_idxbits = bitmask_nwords - 1;
      map->l_gnu_shift = *hash32++;

      map->l_gnu_bitmask = (ElfW(Addr) *) hash32;
      hash32 += __ELF_NATIVE_CLASS / 32 * bitmask_nwords;

      map->l_gnu_buckets = hash32;
      hash32 += map->l_nbuckets;
      map->l_gnu_chain_zero = hash32 - symbias;
      return;
    }
  // ...
}
```

```bash
# readelf --dynamic libtest_gnu_hash.so | grep -E "Tag|GNU_HASH"
  Tag        Type                         Name/Value
 0x000000006ffffef5 (GNU_HASH)           0x260
```

```bash
# readelf --section-headers libtest_gnu_hash.so | grep -E "Nr|260" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 2] .gnu.hash         GNU_HASH         0000000000000260  00000260
       0000000000000038  0000000000000000   A       3     0     8
```

```bash
# export gnu_hash_start_addr=0x260
# export gnu_hash_size=0x38
# od --skip-bytes=$gnu_hash_start_addr --read-bytes=$gnu_hash_size --format=xI libtest_gnu_hash.so
0001140 00000003 00000005 00000001 00000006
0001160 04200400 18012908 00000005 00000008
0001200 00000000 b8f7d29a b95a257a b9d35b69
0001220 6a5ebc3c 6a6128eb
```

##### l_nbuckets / symbias / bitmask_nwords / l_gnu_shift

从 [GNU Hash ELF Sections](https://blogs.oracle.com/solaris/gnu-hash-elf-sections-v2) 摘抄了一段关于 .gnu.hash section 的描述：

> - **l_nbuckets**
>   The number of hash buckets
>
> - **symbias**
>   The dynamic symbol table has *dynsymcount* symbols. *symndx* is the index of the first symbol in the dynamic symbol table that is to be accessible via the hash table. This implies that there are (*dynsymcount* - *symndx*) symbols accessible via the hash table.
>
> - **bitmask_nwords**
>
>   The number of \_\_ELF\_NATIVE\_CLASS sized words in the Bloom filter portion of the hash table section. This value must be non-zero, and must be a power of 2 as explained below.
>
>   Note that a value of 0 could be interpreted to mean that no Bloom filter is present in the hash section. However, the GNU linkers do not do this — the GNU hash section always includes at least 1 mask word.
>
> - **l_gnu_shift**
>   A shift count used by the Bloom filter. HashValue_2 = HashValue_1 >> l_gnu_shift.

对照前面的代码：`l_nbuckets` 是 3 ，`symbias` 是 5 ，`bitmask_nwords` 是 1 ，`l_gnu_shift` 是 6 。

```bash
# readelf --dyn-syms libtest_gnu_hash.so
Symbol table '.dynsym' contains 10 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
     1: 0000000000000000     0 FUNC    WEAK   DEFAULT  UND __cxa_finalize@GLIBC_2.2.5 (2)
     2: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND _ITM_deregisterTMCloneTab
     3: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND __gmon_start__
     4: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND _ITM_registerTMCloneTable
     5: 000000000000110a     7 FUNC    GLOBAL DEFAULT   11 _Z4hahav
     6: 0000000000001111     7 FUNC    GLOBAL DEFAULT   11 _Z4morev
     7: 0000000000001103     7 FUNC    GLOBAL DEFAULT   11 _Z4testv
     8: 00000000000010fc     7 FUNC    GLOBAL DEFAULT   11 _Z3barv
     9: 00000000000010f5     7 FUNC    GLOBAL DEFAULT   11 _Z3foov
```

`symbias` 表明第一个可以通过 .gnu.hash section 访问的符号（即可以提供给其它库访问的符号），在 `libtest_gnu_hash.so` 中这个符号是 `_Z4hahav` 。

##### l_gnu_bitmask

`l_gnu_bitmask` 是 0x260 + 4 * 4 = 0x270 ，`l_gnu_bitmask` 指向 `libtest_gnu_hash.so` 的布隆过滤器；从这个角度看的话，动态链接库的布隆过滤器是由编译器计算的，不是由链接器计算的。

布隆过滤器的原理可以参考文章[详解布隆过滤器的原理，使用场景和注意事项](https://zhuanlan.zhihu.com/p/43263751)，简而言之，将数据使用多个不同的哈希函数生成多个哈希值，并将对应比特位置为 1 ，就能判断某个数据肯定不存在。

参考 [GNU Hash ELF Sections](https://blogs.oracle.com/solaris/gnu-hash-elf-sections-v2) ，构建布隆过滤器的伪代码如下：

```cpp
const uint_fast32_t new_hash = dl_new_hash(undef_name);
uint32_t H1 = new_hash;
uint32_t H2 = new_hash >> map->l_gnu_shift;
uint32_t N = (H1 / __ELF_NATIVE_CLASS) & map->l_gnu_bitmask_idxbits;
unsigned int hashbit1 = H1 % __ELF_NATIVE_CLASS;
unsigned int hashbit2 = H2 % __ELF_NATIVE_CLASS;
bloom[N] |= (1 << hashbit1);
bloom[N] |= (1 << hashbit2);
```

构建布隆过滤器的 C++ 代码如下：

```cpp
// bloom.cpp
#include <ios>
#include <iostream>

uint32_t dl_new_hash(const char *s)
{
  uint32_t h = 5381;
  for (unsigned char c = *s; c != '\0'; c = *++s)
    h = h * 33 + c;
  return h & 0xffffffff;
}

const int __ELF_NATIVE_CLASS = 64;
const int l_gnu_shift = 6;
const int bitmask_nwords = 1;
const int l_gnu_bitmask_idxbits = bitmask_nwords - 1;

void new_bitmask(const char* s, uint64_t* bitmask_arr)
{
  uint32_t hash_value1 = dl_new_hash(s);
  uint32_t hash_value2 = hash_value1 >> l_gnu_shift;
  int n = (hash_value1 / __ELF_NATIVE_CLASS) & l_gnu_bitmask_idxbits;
  unsigned int hashbit1 = hash_value1 % __ELF_NATIVE_CLASS;
  unsigned int hashbit2 = hash_value2 % __ELF_NATIVE_CLASS;
  // Please use 1L (64 bits) instead of 1 (32 bits).
  bitmask_arr[n] |= (1L << hashbit1);
  bitmask_arr[n] |= (1L << hashbit2);
}

int main()
{
  uint64_t bitmask_arr[bitmask_nwords] = {0};
  new_bitmask("_Z4hahav", bitmask_arr);
  new_bitmask("_Z4morev", bitmask_arr);
  new_bitmask("_Z4testv", bitmask_arr);
  new_bitmask("_Z3barv", bitmask_arr);
  new_bitmask("_Z3foov", bitmask_arr);
  std::cout << std::hex << "0x" << bitmask_arr[0] << std::endl;
  // 0x1801290804200400
}
```

##### l_gnu_buckets / l_gnu_chain_zero

`l_gnu_buckets` 指向的一个数组，数组的 `l_nbuckets` 个元素分别是 5、8 和 0 ；5 代表 0 号桶的第一个元素是 `l_gnu_chain_zero[5]` ，8 代表 1 号桶的第一个元素是 `l_gnu_chain_zero[8]` ，0 代表 2 号桶是一个空桶；这是一种用一维数组实现二维数组的手段。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/gnu.hash-implementation.jpeg)

.gnu.hash 实现的是一张二维表，X 轴是哈希表的桶号，Y 轴是符号在 .dynsym 表中的下标，如下图所示：

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/gnu.hash-two-dimensional-table.jpeg)

然而，.gnu.hash 为了节省空间，做了两件非常 tricky 的事情：

1. 将 5 个符号排序（可以发现 5 个符号在 .dynsym 表的顺序并非字母序），使得哈希后处在同一个哈希桶的多个符号彼此相邻，从而将二维表化简成一维表；
2. 将不可导出符号（比如 \_\_cxa\_finalize@GLIBC\_2.2.5 ）排在可导出符号（比如 \_Z3foov）的前面，从而节省掉存储不可导出符号的哈希值的空间；第一个可导出符号在 .dynsym 表的下标记为 `symbias` 。

```cpp
map->l_gnu_chain_zero = hash32 - symbias;
```

将 `l_gnu_chain_zero` 减去 `symbias` ，方便后续计算符号在 .dynsym 表的下标。

#### do_lookup_x

```cpp
// elf/dl-lookup.c
// do_lookup_x
// const uint_fast32_t new_hash = dl_new_hash (undef_name);
const struct link_map *map = list[i]->l_real;
const ElfW(Addr) *bitmask = map->l_gnu_bitmask;
if (__glibc_likely (bitmask != NULL))
{
  ElfW(Addr) bitmask_word
    = bitmask[(new_hash / __ELF_NATIVE_CLASS)& map->l_gnu_bitmask_idxbits];
  unsigned int hashbit1 = new_hash & (__ELF_NATIVE_CLASS - 1);
  unsigned int hashbit2 = ((new_hash >> map->l_gnu_shift)
                           & (__ELF_NATIVE_CLASS - 1));
  if (__glibc_unlikely ((bitmask_word >> hashbit1)
                        & (bitmask_word >> hashbit2) & 1))
  {
    Elf32_Word bucket = map->l_gnu_buckets[new_hash
                                           % map->l_nbuckets];
    if (bucket != 0)
    {
      const Elf32_Word *hasharr = &map->l_gnu_chain_zero[bucket];
      do
        if (((*hasharr ^ new_hash) >> 1) == 0)
        {
          symidx = hasharr - map->l_gnu_chain_zero;
          sym = check_match (undef_name, ref, version, flags,
                             type_class, &symtab[symidx], symidx,
                             strtab, map, &versioned_sym,
                             &num_versions);
          if (sym != NULL)
            goto found_it;
        }
      while ((*hasharr++ & 1u) == 0);
    }
  }
  else
  {
    /* Use the old SysV-style hash table.  Search the appropriate
       hash bucket in this object's symbol table for a definition
       for the same symbol name.  */
    // ...
  }
}
```

##### 哈希算法

```cpp
static uint_fast32_t
dl_new_hash (const char *s)
{
  uint_fast32_t h = 5381;
  for (unsigned char c = *s; c != '\0'; c = *++s)
    h = h * 33 + c;
  return h & 0xffffffff;
}
```

##### 布隆过滤

```cpp
const uint_fast32_t new_hash = dl_new_hash(undef_name);
uint32_t H1 = new_hash;
uint32_t H2 = new_hash >> map->l_gnu_shift;
uint32_t N = (H1 / __ELF_NATIVE_CLASS) & map->l_gnu_bitmask_idxbits;
unsigned int hashbit1 = H1 % __ELF_NATIVE_CLASS;
unsigned int hashbit2 = H2 % __ELF_NATIVE_CLASS;
(bloom[N] & (1 << hashbit1)) && (bloom[N] & (1 << hashbit2));
```

##### 查找哈希表

1. 根据 `l_gnu_buckets` 找到哈希桶的第一个元素；
2. 顺序搜索哈希桶内的元素，直到找到相应的哈希值或者到达结尾。

### 回填 .got.plt 表项

```cpp
const PLTREL *const reloc
  = (const void *) (D_PTR (l, l_info[DT_JMPREL]) + reloc_offset);
void *const rel_addr = (void *)(l->l_addr + reloc->r_offset);
/* Finally, fix up the plt itself.  */
if (__glibc_unlikely (GLRO(dl_bind_not)))
  return value;
return elf_machine_fixup_plt (l, result, refsym, sym, reloc, rel_addr, value);

// sysdeps/x86_64/dl-machine.h
static inline ElfW(Addr)
elf_machine_fixup_plt (struct link_map *map, lookup_t t,
                       const ElfW(Sym) *refsym, const ElfW(Sym) *sym,
                       const ElfW(Rela) *reloc,
                       ElfW(Addr) *reloc_addr, ElfW(Addr) value)
{
  return *reloc_addr = value;
}
```

```cpp
/* Relocation table entry with addend (in section of type SHT_RELA).  */
typedef struct
{
  Elf64_Addr    r_offset;               /* Address */
  Elf64_Xword   r_info;                 /* Relocation type and symbol index */
  Elf64_Sxword  r_addend;               /* Addend */
} Elf64_Rela;
```

```bash
# readelf --dynamic main | grep -E "Tag|JMPREL"
  Tag        Type                         Name/Value
 0x0000000000000017 (JMPREL)             0x578
```

```bash
# readelf --section-headers main | grep -E "Nr|578" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [10] .rela.plt         RELA             0000000000000578  00000578
       0000000000000018  0000000000000018  AI       5    23     8
```

```bash
# export reloc_table_start_addr=0x578
# export reloc_entry_size=0x18
# export reloc_offset=0
# od --skip-bytes=$(($reloc_table_start_addr + $reloc_entry_size * $reloc_offset)) --read-bytes=$reloc_entry_size --format=xL main
0002570 0000000000004018 0000000400000007
0002610 0000000000000000
```

对比 `Elf64_Rela` 的定义，`r_offset` 的值是 0x4018 ，而 0x4018 恰好是 .got.plt 表为函数 foo 预留的占位符。

```bash
# objdump -d -j .plt main | tail -n 3
    1030:   ff 25 e2 2f 00 00       jmpq   *0x2fe2(%rip)        # 4018 <_Z3foov>
    1036:   68 00 00 00 00          pushq  $0x0
    103b:   e9 e0 ff ff ff          jmpq   1020 <.plt>
```

```bash
# readelf --section-headers main | grep -E "Nr|.got.plt" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [23] .got.plt          PROGBITS         0000000000004000  00003000
       0000000000000020  0000000000000008  WA       0     0     8
```

## \_dl\_runtime\_resolve\_xsave: after \_dl\_fixup

```assembly
jmp *%r11               # Jump to function address.
```

\_dl\_runtime\_resolve\_xsave 在调用 \_dl\_fixup 之后的主要工作是：调用函数。

# Others

## 构造 link_map

可执行文件的 `link_map` 由 `dl_main` 函数构造。

## gdb watch

`watch` 能帮助我们找到修改某个值的代码。

```bash
watch *(struct link_map *)0x7ffff7ffe190
```

## l_addr

`l_addr` = 进程中 segment 的虚存地址 - ELF 文件中 segment 的虚存地址 = 0x555555554000

通过 `info proc mappings` 能取得 `l_addr` 。

```bash
# Get the difference between the addresses in the ELF file and the addresses in memory.
# echo "y" | gdb main -ex "start" -ex "set pagination off" -ex "info proc mappings" -ex quit | grep "/root/test/main"
Starting program: /root/test/main
      0x555555554000     0x555555555000     0x1000        0x0 /root/test/main
      0x555555555000     0x555555556000     0x1000     0x1000 /root/test/main
      0x555555556000     0x555555557000     0x1000     0x2000 /root/test/main
      0x555555557000     0x555555558000     0x1000     0x2000 /root/test/main
      0x555555558000     0x555555559000     0x1000     0x3000 /root/test/main
```

# 参考资料

ELF (except .plt and .got.plt and etc.):

+ [Wikipedia: Executable and Linkable Format](https://en.wikipedia.org/wiki/Executable_and_Linkable_Format)
+ [Keith Makan: Introduction to the ELF Format (Part VII): Dynamic Linking / Loading and the .dynamic section](http://blog.k3170makan.com/2018/11/introduction-to-elf-format-part-vii.html)
+ [知乎：写一个工具来了解ELF文件（二）](https://zhuanlan.zhihu.com/p/54399161)
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

Dynamic linking:

+ [Peilin Ye: Understanding \_dl\_runtime\_resolve()](https://ypl.coffee/dl-resolve/)
+ [简书：\_dl\_runtime\_resolve](https://www.jianshu.com/p/57f6474fe4c6)
+ [Understanding Linux ELF RTLD internals](http://s.eresi-project.org/inc/articles/elf-rtld.txt)
+ [Airs – Ian Lance Taylor: Linkers part 1](https://www.airs.com/blog/archives/38)
+ [Airs – Ian Lance Taylor: Linkers part 4](https://www.airs.com/blog/archives/41)
+ [知乎：程序如何从文本文件到ELF文件，再到进程中](https://zhuanlan.zhihu.com/p/96012152)

Debug:

+ [GCC preprocessor with -E and save in file named x](https://stackoverflow.com/questions/41572707/gcc-preprocessor-with-e-and-save-in-file-named-x)
+ [Stack Overflow: How to keep assembly files with --save-temps when multiple targets use the same source file?](https://stackoverflow.com/questions/53810792/how-to-keep-assembly-files-with-save-temps-when-multiple-targets-use-the-same)
+ [GCC Developer Options](https://gcc.gnu.org/onlinedocs/gcc/Developer-Options.html#Developer-Options)
+ [Options Controlling the Preprocessor](https://gcc.gnu.org/onlinedocs/gcc/Preprocessor-Options.html)
+ [Installing as the primary C library](https://tldp.org/HOWTO/Glibc2-HOWTO-5.html)
+ [glibc wiki: Debugging the Loader](https://sourceware.org/glibc/wiki/Debugging/Loader_Debugging)
+ [Super User: overwrite default /lib64/ld-linux-x86-64.so.2 to call executables](https://superuser.com/questions/1144758/overwrite-default-lib64-ld-linux-x86-64-so-2-to-call-executables)
+ [Stack Overflow: Locating the Global Offset Table in an ELF file](https://stackoverflow.com/questions/32947936/locating-the-global-offset-table-in-an-elf-file)
+ [知乎：x86_64 架构下的函数调用及栈帧原理](https://zhuanlan.zhihu.com/p/107455887)
+ [Stack Overflow: What is the jmpq command doing in this example](https://stackoverflow.com/questions/26543029/what-is-the-jmpq-command-doing-in-this-example)

Others:

+ [Executable and Linkable Format 101 Part 3: Relocations](https://www.intezer.com/blog/elf/executable-and-linkable-format-101-part-3-relocations/)
+ [Pasky’s Log: ld.so Scopes](http://log.or.cz/?tag=suse)