---
layout: post
title: "Dynamic Linking: Compatibility Of Hash Tables"
date: 2020-12-22 10:43:35
categories:
  - [Computer Science, Dynamic Linking]
---

# 导读

1. 指定编译选项 `-Wl,--hash-style=both` 时，dynsym section 的符号排列顺序需要满足 gnu hash table 的要求，具体可参考 [Dynamic Linking: Search Symbols In One Binary](https://clcanny.github.io/2020/11/20/dynamic-linking-search-symbols-in-one-binary/) ：
    1. LOCAL 符号排在 GLOBAL 符号之前；
    2. 导入符号排在导出符号之前；
    3. 导出符号按桶排序；
2. [ELF: symbol lookup via DT\_HASH](https://flapenguin.me/elf-dt-hash) 将 SysV hash table 讲得非常清楚：
    1. SysV hash table 的长度和 dynamic symbol table 的长度相同；
    2. bucket 记录每个桶的起始符号；
    3. chain 是 dynamic symbol table 的附属指针数组；
    4. chain[id] 将 Ndx = STN_UNDEF 的符号作为结束符。

# SysV hash table 详解

```cpp
// test_hash.cpp
// g++ -std=c++11 -shared -fPIC -Wl,--hash-style=both test_hash.cpp -o libtest_hash.so
void foo() {}
void bar() {}
void test() {}
void haha() {}
void more() {}
```

## 元数据

```c
void _dl_setup_hash(struct link_map* map) {
  if (__glibc_likely(map->l_info[ADDRIDX(DT_GNU_HASH)] != NULL)) {
    // ...
    return;
  }

  if (!map->l_info[DT_HASH]) {
    return;
  }
  // The entries in the .hash table always have a size of 32 bits.
  Elf_Symndx* hash = (void*)D_PTR(map, l_info[DT_HASH]);
  map->l_nbuckets = *hash++;
  // Skip nchain.
  hash++;
  map->l_buckets = hash;
  hash += map->l_nbuckets;
  map->l_chain = hash;
}
```

```cpp
struct elf_hash_table {
  uint32_t nbucket;
  uint32_t nchain;
  uint32_t bucket[nbucket];
  uint32_t chain[nchain];
};
```

```bash
# readelf --section-headers libtest_hash.so  | grep -E "Nr|hash" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [ 2] .hash             HASH             00000000000001b8  000001b8
       0000000000000058  0000000000000004   A       4     0     8
  [ 3] .gnu.hash         GNU_HASH         0000000000000210  00000210
       000000000000004c  0000000000000000   A       4     0     8
# export hash_start_addr=0x1b8
# export hash_size=0x58
# od --skip-bytes=$hash_start_addr --read-bytes=$hash_size --format=xI libtest_hash.so
0000670 00000003 00000011 0000000f 0000000a
0000710 0000000e 00000000 00000000 00000000
0000730 00000002 00000009 00000004 00000008
0000750 00000000 00000000 00000010 00000005
0000770 0000000d 00000003 0000000c 00000006
0001010 0000000b 00000007
```

| nbucket | nchain | bucket[bucket]  | chain[nchain] |
|   :-:   |  :-:   |       :-:       |      :-:      |
|   0x3   |  0x11  | [0xf, 0xa, 0xe] |  [0x0, ...]   |

```bash
# readelf --dyn-syms libtest_hash.so
Symbol table '.dynsym' contains 17 entries:
   Num:    Value          Size Type    Bind   Vis      Ndx Name
     0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND
     1: 0000000000000608     0 SECTION LOCAL  DEFAULT   10
     2: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND __gmon_start__
     3: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND _Jv_RegisterClasses
     4: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND _ITM_deregisterTMCloneTab
     5: 0000000000000000     0 NOTYPE  WEAK   DEFAULT  UND _ITM_registerTMCloneTable
     6: 0000000000000000     0 FUNC    WEAK   DEFAULT  UND __cxa_finalize@GLIBC_2.2.5 (2)
     7: 000000000000075a     6 FUNC    GLOBAL DEFAULT   12 _Z4hahav
     8: 0000000000000760     6 FUNC    GLOBAL DEFAULT   12 _Z4morev
     9: 0000000000000754     6 FUNC    GLOBAL DEFAULT   12 _Z4testv
    10: 0000000000200b08     0 NOTYPE  GLOBAL DEFAULT   23 _end
    11: 0000000000200b00     0 NOTYPE  GLOBAL DEFAULT   22 _edata
    12: 000000000000074e     6 FUNC    GLOBAL DEFAULT   12 _Z3barv
    13: 0000000000000748     6 FUNC    GLOBAL DEFAULT   12 _Z3foov
    14: 0000000000200b00     0 NOTYPE  GLOBAL DEFAULT   23 __bss_start
    15: 0000000000000608     0 FUNC    GLOBAL DEFAULT   10 _init
    16: 0000000000000768     0 FUNC    GLOBAL DEFAULT   13 _fini
```

nchain 是 17 ，chain 的长度是 17 ，dynamic symbol table 有 17 个 entries 。

## 哈希函数

```cpp
#include <cstdint>
#include <ios>
#include <iostream>
#include <vector>

uint32_t elf_hash(const char* name) {
  uint32_t h = 0, g;
  for (; *name; name++) {
    h = (h << 4) + *name;
    if (g = h & 0xf0000000) {
      h ^= g >> 24;
    }
    h &= ~g;
  }
  return h;
}

int main() {
  std::cout << std::hex;
  std::vector<const char*> symbol_names{"_Z4hahav",
                                        "_Z4morev",
                                        "_Z4testv",
                                        "_Z3barv",
                                        "_Z3foov",
                                        "_end",
                                        "_edata",
                                        "__bss_start",
                                        "_init",
                                        "_fini"};
  for (const char* symbol_name : symbol_names) {
    std::cout << "0x" << elf_hash(symbol_name) << std::endl;
  }
}
```

| dynsym\_id |  symbol\_name  | hash\_value | bucket\_id |
|    :-:     |      :-:       |     :-:     |    :-:     |
|     7      |   \_Z4hahav    |  0xdae78c6  |     1      |
|     8      |   \_Z4morev    |  0xdb46e86  |     2      |
|     9      |   \_Z4testv    |  0xdbaccf6  |     1      |
|     10     |     \_end      |   0x65c44   |     1      |
|     11     |    \_edata     |  0x65ba8a1  |     0      |
|     12     |    \_Z3barv    |  0x4d988f6  |     0      |
|     13     |    \_Z3foov    |  0x4d9d606  |     0      |
|     14     | \_\_bss\_start |  0x90ff134  |     2      |
|     15     |     \_init     |  0x660504   |     0      |
|     16     |     \_fini     |  0x65d049   |     1      |

## 哈希表

![](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-compatibility-of-hash-tables/hash-table.png)

# 参考资料

+ [ELF: symbol lookup via DT\_HASH](https://flapenguin.me/elf-dt-hash)
+ [A Fast LKM loader based on SysV ELF hash table](https://elinux.org/images/1/18/C_AMOROSO_Fast_lkm_loader_ELC-E_2009.pdf)
+ [AnSwEr's Blog ：\-\-hash-style 兼容性问题](https://answerywj.com/2020/05/14/ld-hash-style/)
+ [Oracle: Hash Table Section](https://docs.oracle.com/cd/E23824_01/html/819-0690/chapter6-48031.html)
