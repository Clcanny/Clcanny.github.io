---
layout: post
title: "Dynamic Linking: Search Symbols In One Binary"
date: 2020-11-20 01:28:45
tags:
  - dynamic linking
---

# 导读

[Dynamic Linking: Symbol Search Order](https://clcanny.github.io/2020/11/18/dynamic-linking-symbol-search-order/) 介绍了在多个文件间查找符号的顺序，本篇文章会聚焦于 `do_lookup_x` 函数，探讨在单文件内查找符号的步骤：

1. 布隆过滤器和哈希表是两个重要的数据结构；
2. 它们是由编译器而不是运行时链接器准备的。

# Code

## 加载 .gnu.hash section

```c
struct link_map {
  // ...
  // Symbol hash table.
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
  const ElfW(Addr) * l_gnu_bitmask;
  union {
    const Elf32_Word* l_gnu_buckets;
    const Elf_Symndx* l_chain;
  };
  union {
    const Elf32_Word* l_gnu_chain_zero;
    const Elf_Symndx* l_buckets;
  };
  // ...
};
```

```c
void _dl_setup_hash(struct link_map* map) {
  if (__glibc_likely(map->l_info[ADDRIDX(DT_GNU_HASH)] != NULL)) {
    Elf32_Word* hash32 = (void*)D_PTR(map, l_info[ADDRIDX(DT_GNU_HASH)]);
    map->l_nbuckets = *hash32++;
    Elf32_Word symbias = *hash32++;
    Elf32_Word bitmask_nwords = *hash32++;
    // Must be a power of two.
    assert((bitmask_nwords & (bitmask_nwords - 1)) == 0);
    map->l_gnu_bitmask_idxbits = bitmask_nwords - 1;
    map->l_gnu_shift = *hash32++;

    map->l_gnu_bitmask = (ElfW(Addr)*)hash32;
    hash32 += __ELF_NATIVE_CLASS / 32 * bitmask_nwords;

    map->l_gnu_buckets = hash32;
    hash32 += map->l_nbuckets;
    map->l_gnu_chain_zero = hash32 - symbias;
    return;
  }
  // ...
}
```

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
>   A shift count used by the Bloom filter. HashValue\_2 = HashValue\_1 >> l\_gnu\_shift.

## 哈希算法

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

## 查找符号

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

# 详解

```cpp
// test_gnu_hash.cpp
// g++ -std=c++11 -shared -fPIC test_gnu_hash.cpp -o libtest_gnu_hash.so
void foo() {}
void bar() {}
void test() {}
void haha() {}
void more() {}
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

|       | l\_nbuckets | symbias | bitmask\_nwords | l\_gnu\_bitmask_idxbits | l\_gnu\_shift |  l\_gnu\_bitmask   | l\_gnu\_buckets |                l\_gnu\_chain\_zero + symbias                 |
|  :-:  |     :-:     |   :-:   |       :-:       |           :-:           |      :-:      |        :-:         |       :-:       |                             :-:                              |
| value |     0x3     |   0x5   |       0x1       |           0x0           |      0x6      | 0x1801290804200400 | [0x5, 0x8, 0x0] | [0xb8f7d29a, 0xb95a257a, 0xb9d35b69, 0x6a5ebc3c, 0x6a6128eb] |

## 哈希表

编译器实现哈希表时用了几个技巧：

1. 用一维数组 `l_gnu_chain_zero + symbias` 实现二维哈希表：
    1. 将在同一个哈希桶内的元素放在数组的连续区域；
    2. 用另一个一维数组 `l_gnu_buckets` 记录哈希桶的起始位置；
    3. 约定哈希桶的最后一个元素的最后一个比特是 1 ，其余元素的最后一个比特是 0 ；
2. 为节省哈希表空间：
    1. 哈希表只记录哈希值，不记录符号在 .dynsym 表中的下标；
    2. 哈希表只记录可导出符号（比如 \_Z3foov ）的哈希值，不记录不可导出符号（比如 \_\_cxa\_finalize@GLIBC\_2.2.5 ）的哈希值；
    3. 为同时达到以上两个目标，编译器在 .dynsym 表中将不可导出符号（比如 \_\_cxa\_finalize@GLIBC\_2.2.5 ）排在可导出符号（比如 \_Z3foov ）的前面，将第一个可导出符号在 .dynsym 表中的下标记为 `symbias` ，计算 `l_gnu_chain_zero` 的公式是 `map->l_gnu_chain_zero = map->l_gnu_buckets + map->l_nbuckets - symbias` 。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-search-symbols-in-one-binary/one-dimensional-hash-table.png)

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-search-symbols-in-one-binary/two-dimensional-hash-table.png)

| id  |   name    | new\_hash  | 处理最后一个比特后 | bucket |
| :-: |    :-:    |    :-:     |        :-:         |  :-:   |
|  5  | \_Z4hahav | 0xb8f7d29a |     0xb8f7d29a     |   0    |
|  6  | \_Z4morev | 0xb95a257b |     0xb95a257a     |   0    |
|  7  | \_Z4testv | 0xb9d35b68 |   **0xb9d35b69**   |   0    |
|  8  | \_Z3barv  | 0x6a5ebc3c |     0x6a5ebc3c     |   1    |
|  9  | \_Z3foov  | 0x6a6128eb |   **0x6a6128eb**   |   1    |

加粗部分是每个哈希桶的最后一个元素，最后一个比特需要置成 1 。

1. 根据 `l_gnu_buckets` 找到哈希桶的第一个元素；
2. 顺序搜索哈希桶内的元素，直到找到相应的哈希值或者到达结尾。

### symbias

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

## 布隆过滤器

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

# More

编译器如何处理哈希冲突？

# 参考资料

+ [GNU Hash ELF Sections](https://blogs.oracle.com/solaris/gnu-hash-elf-sections-v2)
+ [知乎：详解布隆过滤器的原理，使用场景和注意事项](https://zhuanlan.zhihu.com/p/43263751)
