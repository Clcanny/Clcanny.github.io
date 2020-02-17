---
title: tcmalloc
date: 2020-02-17 16:05:00
tags:
---

# 背景

TOMA = TCMalloc-based Object-oriented Memory Anaslyer

TOMA 是一个用于分析 C++ 程序内存占用的工具，这个工具利用 TCMalloc 提供的信息，将面向字节的内存分析转变成面向对象的分析工具，顺便提供了以下几种常用的工具：

1. 根据地址找出内存对象
2. 提供对象的指向关系
3. 识别常见对象（含虚表的对象、Lua 对象、Java 对象……）
4. 识别运行中的线程及其堆栈
5. 识别已销毁的堆栈

TOMA 系列文章会介绍TOMA 工具开发过程中用到的关键技术：

1. 基于字节读取 coredump 文件
2. 根据 TCMalloc 读取对象信息
3. 快速扫描对象指针关系
4. NPTL 与识别运行中的线程及其堆栈
5. 堆栈 call convention 与猜测已销毁的堆栈
6. 虚表结构与识别含虚表的对象
7. 识别 Lua 对象
8. 识别 Java 对象

# 环境信息

```shell
readelf -d libtcmalloc.so | grep SONAME
0x000000000000000e (SONAME) Library soname: [libtcmalloc.so.4]
```

```shell
uname --m
x86_64
```

```shell
wget https://github.com/gperftools/gperftools/archive/gperftools-2.0.tar.gz
tar -xzvf gperftools-2.0.tar.gz
cd gperftools-gperftools-2.0
./configure --enable-minimal --prefix=$PWD/build
make -j60
make install
```

以下源代码的版本是 gperftools-gperftools-2.0

截止笔者写这篇文章的时间（2019-11-01），tcmalloc 最新的版本是 gperftools-2.7

# TCMalloc 概述

感谢 wallen 写的[TCMalloc 解密](https://wallenwang.com/2018/11/tcmalloc/#ftoc-heading-62)，这是我认为在网上能找到的关于 TCMalloc 写得最好的中文文章，本小节中的内容大多是对该文章的再次加工，图片更是全来源于这篇文章。

由于我们更关心如何找出正在使用中的对象，所以省略了 TCMalloc 分配与回收算法的介绍，并且也更加精简数据结构的介绍以突出重点。这一小节介绍的是逻辑概念，一些概念在 TCMalloc 的实现中是没有对应数据结构的。

一图胜千言，从图中我们可以得出使用中的对象的计算方法：

使用中的对象 = PageHeap 中的对象 - CentralCache 中的对象 - ThreadCache 中的对象

![](tcmalloc-Overview.svg)

## PageHeap

1. Page 是 TCMalloc 对虚拟内存的抽象，可以近似地将 Page 理解成虚拟内存页
2. Span 由一页或多页连续的 Page 构成，是 PageHeap 管理内存页的基本单位
3. PageHeap 用于管理 Span

![](tcmalloc-PageHeap.svg)

### PageMap

PageMap 协助 PageHeap 管理 Span ，回答这样一个问题：给定一个 PageId ，如何确定它属于哪一个 Span ？

不妨将 PageMap 设想成一个长度为 page size 的数组，下标是 PageId ，值是指向 Span 的指针

实际实现中，PageMap 将采用二级或三级 radix tree （多级索引）以节省存储空间：

![](tcmalloc-PageMap.svg)

## CentralCache

1. TCMalloc 根据对象的大小将小对象分类，一共有 85 类（不包括 0 字节大小的对象）
2. 只有这 85 类对象会被 CentralCache 和 ThreadCache 缓存
3. CentralCache 是一个逻辑概念，实现上对应的是 CentralFreeList 类型的数组
4. CentralFreeList 真正管理的是 Span ，而小对象被包含在 Span 的空闲对象链表中，所以 CentralCache 实际上由每一个 Span 的空闲对象列表构成
5. CentralFreeList 的 `empty_` 链表保存了已经没有空闲对象可用的 Span，`nonempty_` 链表保存了还有空闲对象可用的 Span

![](tcmalloc-CentralCache.svg)

![](tcmalloc-CentralFreeList.svg)

## ThreadCache

ThreadCache 是独属于每一个线程的小对象缓存系统

![](tcmalloc-ThreadCache.svg)

# 探索 TCMalloc 的细节

本小节探索 TCMalloc 中对 TOMA 有影响的数据结构，数据结构均从 gperftools-gperftools-2.0 中整理得到

数据结构相比于原版去除了宏以方便理解，且通过验证（因为力求可以直接使用，所以未做省略，导致稍显详细）

## SizeMap

## Page

```cpp
// 64 = 16 (unused) + 12 (levelA) + 12 (levelB) + 11 (levelC) + 13 (pageShift)
const int kUnusedBits = 16;
const int kPageIdBits = 35;

const int kInteriorBits = 12;
const int kLeafBits = 11;
const int kPageBits = 13;
```

在 64 位机器中，高 16 位永远为 0 ，暂未被使用

TCMalloc 的 Page 大小默认是 8K = 2^13 ，低 13 位构成页内偏移

剩下的 35 位构成 radix tree 的三级索引，分别是 12 / 12 / 11

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc/page-and-span.jpeg)

## Span

```cpp
struct Span {
    // origin name: start
    uint64_t mStartPageId;
    // origin name: length
    uint64_t mPageNum;
    Span* mNext;
    Span* mPrev;
    void* mObjects;
    // origin name: refcount
    unsigned int mNonFreeObjectNum : 16;
    unsigned int mClassId : 8;
    unsigned int mLocation : 2;
    unsigned int mSample : 1;

    // possible values of mLocation
    enum { eInUse = 0, eNormal = 1, eReturned = 2 };
};
```

1. mNext / mPrev 用于构建双向环形链表，链表头存放与 CentralFreeList 类型的数组中
2. mObjects 存储页内空闲对象列表
3. mNonFreeObjectNum 记录页内非空闲对象数
4. mLocation 记录页状态：使用中（拆分成小对象缓存或分配给应用程序）、缓存中、已归还给操作系统

## PageHeap

```cpp
struct PageHeap {
    PageMap3 mPagemap;
    PackedCache mPagemapCache;
    SpanList mLargeFree;
    SpanList mSmallFree[kSmallSpanMaxPage];
    uint8_t mStats[24];
    int64_t mScavengeCounter;
    int mReleaseIndex;
};
```

```cpp
const int kSmallSpanMaxPage = 128;
```

1. mPagemap 记录着 PageId 与 Span 的对应关系（这将是我们找出所有 Span 的重要字段）
2. mPagemapCache 是 mPagemap 的缓存（我们不使用这个字段）
3. mLargeFree / mSmallFree 缓存未使用的 Span （分配出去的 Span 不由 PageHeap 管理，Span 指针在 mPagemap 中有记录）

### PageMap3

```cpp
struct PageMap3 {
    LevelANode* mRoot;
    void* (*mAlloc)(uint64_t);
};
```

```cpp
struct LevelCNode {
    Span* mPtrs[kLeafLength];
    Span* operator[](int i) const;
};

struct LevelBNode {
    LevelCNode* mPtrs[kInteriorLength];
    LevelCNode* operator[](int i) const;
};

struct LevelANode {
    LevelBNode* mPtrs[kInteriorLength];
    LevelBNode* operator[](int i) const;
};
```

PageMap3 的实现非常简单、直观，是一个 3 级 radix tree

### PackedCache

```cpp
struct PackedCache {
    uint64_t array_[1 << 16];

    static const int kKeyBits = 35;
    static const uint64_t kKeyMask = (1L << kKeyBits) - 1;
    static const int kValueBits = 7;
    static const uint64_t kValueMask = (1 << kValueBits) - 1;
    static const int kHashBits = 16;
    static const uint64_t kHashMask = (1 << kHashBits) - 1;

    // origin name: GetOrDefault
    // default value = 0
    std::size_t Get(uint64_t key) const;
};
```

PackedCache 是 PageMap3 的缓存，实现很巧妙（篇幅关系，这里不展开）

### SpanList

```cpp
struct SpanList {
    Span mNormal;
    Span mReturned;
};
```

## CentralCache

TCMalloc 的实现中没有 CentralCache 这个类，我们为了方便 CentralCache 作为返回值类型使用，创建了这个类

```cpp
// C++ can't return array, so we can't use array directly.
// using CentralCache = CentralFreeList[kNumClasses];
struct CentralCache {
    CentralFreeList mCentralFreeLists[kNumClasses];
    CentralFreeList operator[](int i) const;
};
```

CentralCache 就是由 CentralFreeList 构成的数组

### CentralFreeList

```cpp
struct CentralFreeList {
    uint8_t mSpinLock[4];

    std::size_t mClassId;
    Span mEmptySpan;
    Span mNonEmptySpan;
    // Number of spans in mEmptySpan plus mNonEmptySpan
    std::size_t mNumSpans;
    // origin name: counter_
    // not include free objects in tcSlots
    std::size_t mInSpanFreeObjNum;

    TCEntry mTcSlots[kTcSlotSize];
    int32_t mUsedSlots;
    int32_t mCacheSize;
    int32_t mMaxCacheSize;

    int8_t mPad[48];
};
```

1. mEmptySpan / mNonEmptySpan 分别存储所有对象未被使用的 Span 和有对象被使用的 Span
2. mUsedSlots 记录使用中 mTcSlots 的大小
3. mCacheSize 是 mUsedSlots 的上限
4. mMaxCacheSize 是 mCacheSize 的上限，它对于某一类对象而言是一个固定值

#### TCEntry

CentralFreeList 和 ThreadCache之间的对象移动有个优化措施，因为大部分情况都是每次移动 batch_size 个对象，为了减少链表操作，提升效率，CentralFreeList 将移动的 batch_size 个对象的链表的首尾指针缓存在了TCEntry 中。因此后续只要需要移动 batch_size 个对象，只需要操作链表的首尾即可。

```cpp
struct TCEntry {
    void* mHead;
    void* mTail;
};
```

## ThreadCache

```cpp
struct ThreadCache {
    ThreadCache* mNext;
    ThreadCache* mPrev;

    // origin name: size
    std::size_t mCacheSizeInByte;
    std::size_t mMaxSize;
    uint8_t mSampler[16];
    FreeList mFreeList[kNumClasses];
    uint64_t mTid;
    bool mInSetSpecific;
};
```

1. mMaxSize 是 mCacheSizeInByte 的上限？（这一条在实际使用 TOMA 时出现过反例）

# 寻找使用中的对象

# reference

1. [TCMalooc 解密](https://wallenwang.com/2018/11/tcmalloc/)

