---
layout: post
title: "Dynamic Linking: Relocation Across Files"
date: 2020-11-21 00:11:51
tags:
  - dynamic linking
---

# 开始重定位：.plt .got.plt

.plt 和 .got.plt 配合完成 lazy binding ，图片摘抄自 [LIEF: 05 - Infecting the plt/got](https://lief.quarkslab.com/doc/latest/tutorials/05_elf_infect_plt_got.html) ：

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-relocation-across-files/plt-got-mechanism-first-time-call.jpg)

*With lazy binding, the first time that the function is called the* `got` *entry redirects to the plt instruction.*

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-relocation-across-files/plt-got-mechanism-second-time-call.jpg)

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

# \_dl\_runtime\_resolve\_xsave: before \_dl\_fixup

`_dl_runtime_resolve_xsave` 定义于 /root/glibc/glibc-2.28/sysdeps/x86_64/dl-trampoline.h ，不过文件内大量使用 `#if` 语句，并不适合直接阅读。

\_dl\_runtime\_resolve\_xsave 在调用 \_dl\_fixup 之前的主要工作是：保存寄存器。

# \_dl\_fixup

`_dl_runtime_resolve_xsave` 的核心是位于 elf/dl-runtime.c 的 `_dl_fixup` ，`_dl_fixup` 的执行过程如下：

1. 用 `link_map` 访问 .dynamic ，分别取出 .rela.plt / .dynsym / .dynstr 的地址；
2. .rela.plt + 参数 `reloc_arg` ，求出当前函数的重定位表项 Elf64_Rela 的指针，记作 reloc ；
3. 以 `ELFW(R_SYM) (reloc->r_info)` 作为 .dynsym 的下标，求出当前函数的符号表项 `Elf64_Sym` 的指针，记作 `sym` ；
4. `.dynstr + sym->st_name` 得出符号名字 ；
5. 在动态链接库中查找这个函数的地址，并且把地址赋值给 `*(reloc->r_offset)` ，即 .got.plt 表项 。

## 访问 .dynamic 表项

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

## 对比 .dynamic 与 section headers

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

## 访问 .rela.plt 表项

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

## 访问 .dynsym 表项

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

## 访问 .dynstr 表项

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

## 查找符号

`_dl_lookup_symbol_x` 遍历 `l->l_scope` ，对于每一个 `scope` 调用 `do_lookup_x` 函数寻找符号：

1. [Dynamic Linking: Symbol Search Order](https://clcanny.github.io/2020/11/18/dynamic-linking-symbol-search-order/) 探讨了在多个文件间查找符号的顺序；
2. [Dynamic Linking: Search Symbols In One Binary](https://clcanny.github.io/2020/11/20/dynamic-linking-search-symbols-in-one-binary/) 探讨了在多个文件间查找符号的顺序。

### l\_scope

摘抄自 [ld.so Scopes](http://log.or.cz/?p=129) ：

> The scope describes which libraries should be searched for symbol lookups occuring within the scope owner. (By the way, given that lookup scope may differ by caller, implementing `dlsym()` is not *that* trivial.) It is further divided into **scope elements (struct r_scope_elem)** – a single scope element basically describes a single search list of libraries, and the scope (**link_map.l_scope** is the scope used for symbol lookup) is list of such scope elements.

> To reiterate, a symbol lookup scope is a list of lists! Then, when looking up a symbol, the linker walks the lists in the order they are listed in the scope. But what really are the scope elements? There are two usual kinds:
>
> - The "global scope" – all libraries (ahem, link_maps) that have been requested to be loaded by the main program (what ldd on the binary file of the main program would print out, plus dlopen()ed stuff).
> - The "local scope" – DT_NEEDED library dependencies of the current link_map (what ldd on the binary file of the library would print out, plus dlopen()ed stuff).

> The global scope is shared between all link_maps (in the current namespace), while the local scope is owned by a particular library.

## 回填 .got.plt 表项

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

# \_dl\_runtime\_resolve\_xsave: after \_dl\_fixup

```assembly
jmp *%r11               # Jump to function address.
```

`_dl_runtime_resolve_xsave` 在调用 `_dl_fixup` 之后的主要工作是：调用函数。
