---
layout: post
title: "Dynamic Linking: Search Symbols In One Binary"
date: 2020-11-20 01:28:45
tags:
  - dynamic linking
---

# 导读

[Dynamic Linking: Symbol Search Order](https://clcanny.github.io/2020/11/18/dynamic-linking-symbol-search-order/) 介绍了在多个文件间查找符号的顺序，本篇文章会聚焦于 `do_lookup_x` 函数，探讨在单文件内查找符号的步骤及关键的数据结构和算法：

1. 布隆过滤；
2. 哈希表。

# 哈希表

编译器会准备好哈希表。

## Code

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

## 例子

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

# 哈希表
