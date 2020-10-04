# Dynamic Link

## 环境

```dockerfile
FROM debian:buster
LABEL maintainer="837940593@qq.com"

ENV DEBIAN_FRONTEND noninteractive
RUN apt-get update
RUN apt-get install -y build-essential make gcc g++ gdb

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
RUN make all -j8 && make install

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

## 动态链接的一个小例子

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

## 从 ELF 文件看动态链接

### 工具概述

#### Dump 二进制

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

#### Dump 汇编代码

```bash
# objdump -d libfoo.so --start-address=0x1020 --stop-address=$((0x1020+0x10))
0000000000001020 <.plt>:
    1020:   ff 35 e2 2f 00 00       pushq  0x2fe2(%rip)  # 4008 <_GLOBAL_OFFSET_TABLE_+0x8>
    1026:   ff 25 e4 2f 00 00       jmpq   *0x2fe4(%rip) # 4010 <_GLOBAL_OFFSET_TABLE_+0x10>
    102c:   0f 1f 40 00             nopl   0x0(%rax)
```

#### Dump 元信息

```bash
# readelf --file-header main
# readelf --program-headers main
# readelf --section-headers main
```

#### 解析特定 sections

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

### ELF 文件概述

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking/ELF_Executable_and_Linkable_Format_diagram_by_Ange_Albertini.png)

File Header 和 Program Header 在 ELF 文件的开头，Section Header 在 ELF 文件的结尾。

接下来我们会用 readelf 直接查看元数据，也会用 od 以二进制方式看看每一个 Header 。

#### File Header

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

#### Program Header

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

#### Section Header

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

### 重定位

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

#### 构造 link_map

### .got .plt .got.plt .plt.got

### .dynamic

## 从运行时看动态链接

根据 [Understanding Linux ELF RTLD internals](http://s.eresi-project.org/inc/articles/elf-rtld.txt) 的描述，the dynamic linker source code hierarchy 如下：

```txt
_dl_main()
  process_envvars()
  _dl_new_object()
```

### _dl_runtime_resolve_xsave 执行过程

`_dl_runtime_resolve_xsave` 定义于 /root/glibc/glibc-2.28/sysdeps/x86_64/dl-trampoline.h ，不过文件内大量使用 `#if` 语句，并不适合直接阅读。

根据 [_dl_runtime_resolve](https://www.jianshu.com/p/57f6474fe4c6) 的描述，`_dl_runtime_resolve_xsave` 的执行过程分为几步：

1. 用 link_map 访问 .dynamic ，分别取出 .dynstr、.dynsym、.rel.plt 的地址

2. .rel.plt + 参数 `relic_index` ，求出当前函数的重定位表项 Elf32_Rel 的指针，记作 rel

3. `rel->r_info >> 8` 作为 .dynsym 的下标，求出当前函数的符号表项 `Elf32_Sym` 的指针，记作 `sym`

4. `.dynstr` + `sym->st_name`得出符号名字符串指针

5. 在动态链接库查找这个函数的地址，并且把地址赋值给`*rel->r_offset`，即`GOT`表

6. 调用这个函数

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

`l_addr` = 进程中 segment 的虚存地址 - ELF 文件中 segment 的虚存地址 = 0x555555554000

### _dl_fixup 

`_dl_runtime_resolve_xsave` 的核心是位于 elf/dl-runtime.c 的 `_dl_fixup` ，接下来我们会跟着代码一步一步地解析 ELF 文件。

#### 访问 .dynamic 表项

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

##### 对比 .dynamic 与 section headers

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

#### 访问 .rela.plt 表项

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

#### 访问 .symtab 表项

```cpp
/* We use this macro to refer to ELF macros independent of the native
   wordsize.  `ELFW(R_TYPE)' is used in place of `ELF32_R_TYPE' or
   `ELF64_R_TYPE'.  */
#define ELFW(type)      _ElfW (ELF, __ELF_NATIVE_CLASS, type)
#define ELF64_R_SYM(i)			((i) >> 32)

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

#### 访问 .strtab 表项

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
# export string_table_start_addr=0x3f0
# export st_name=0x50
# od --skip-bytes=$(($string_table_start_addr + $st_name)) --read-bytes=0x8 --format=xC -c main
0002100  5f  5a  33  66  6f  6f  76  00
          _   Z   3   f   o   o   v  \0
```

函数 `foo` 在 mangle 后的名字是 `_Z3fooV` 。

#### 查找符号

`_dl_lookup_symbol_x` 是怎么根据字符串找到函数地址的？

根据 [Symbol Versioning](https://gcc.gnu.org/wiki/SymbolVersioning) 的说法：In general, this capability exists only on a few platforms. Symbol Versioning 不是一种普遍的做法。

