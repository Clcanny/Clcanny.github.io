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

感谢 wallen 写的[TCMalloc 解密](https://wallenwang.com/2018/11/tcmalloc/#ftoc-heading-62)，这是我认为在网上能找到的、关于 TCMalloc 写得最好的中文文章，本小节中的内容大多是对该文章的再次加工，图片更是全来源于这篇文章。

由于我们更关心如何找出正在使用中的对象，所以省略了 TCMalloc 分配与回收算法的介绍，并且也更加精简数据结构的介绍以突出重点。这一小节介绍的是逻辑概念，一些概念在 TCMalloc 的实现中是没有对应数据结构的。

一图胜千言，从图中我们可以得出使用中的对象的计算方法：

使用中的对象 = PageHeap 中的对象 - CentralCache 中的对象 - ThreadCache 中的对象

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/Overview.svg)

## PageHeap

1. Page 是 TCMalloc 对虚拟内存的抽象，可以近似地将 Page 理解成虚拟内存页
2. Span 由一页或多页连续的 Page 构成，是 PageHeap 管理内存页的基本单位
3. PageHeap 用于管理 Span

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/PageHeap.svg)

### PageMap

PageMap 协助 PageHeap 管理 Span ，回答这样一个问题：给定一个 Page ，如何确定它属于哪一个 Span ？

不妨将 PageMap 设想成一个长度为 page size 的数组，下标是 PageId ，值是指向 Span 的指针

在 TCMalloc 的实现中，PageMap 将采用二级或三级 radix tree （多级索引）以节省存储空间：

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/PageMap.svg)

## CentralCache

1. TCMalloc 根据对象的大小将小对象分类，一共有 85 类（不包括 0 字节大小的对象）
2. 只有这 85 类对象会被 CentralCache 和 ThreadCache 缓存
3. CentralCache 是一个逻辑概念，实现上对应的是 CentralFreeList 类型的数组
4. CentralFreeList 真正管理的是 Span ，而小对象被包含在 Span 的空闲对象链表中，所以 CentralCache 实际上由每一个 Span 的空闲对象列表构成
5. CentralFreeList 的 `empty_` 链表保存了已经没有空闲对象可用的 Span，`nonempty_` 链表保存了还有空闲对象可用的 Span

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/CentralCache.svg)

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/CentralFreeList.svg)

## ThreadCache

ThreadCache 是独属于每一个线程的小对象缓存系统

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/ThreadCache.svg)

# 探索 TCMalloc 的细节

本小节探索 TCMalloc 中对 TOMA 有影响的数据结构，数据结构均从 gperftools-gperftools-2.0 中整理得到

数据结构相比于原版去除了宏以方便理解，且通过验证（因为力求可以直接使用，所以未做省略，导致稍显详细）

以下会介绍几个关键的类：

+ SizeMap 定义了小对象、Page 说明了 PageId 的构成、Span 是 TCMalloc 管理内存页的基本单位
+ PageHeap / CentralCahe / ThreadCache 是计算对象的重要数据结构

## SizeMap

```cpp
class SizeMap {
 private:
    ClassSize mTable[kNumClasses] = {
        0,      8,      16,     32,     48,     64,     80,     96,     112,
        128,    144,    160,    176,    192,    208,    224,    240,    256,
        288,    320,    352,    384,    416,    448,    480,    512,    576,
        640,    704,    768,    896,    1024,   1152,   1280,   1408,   1536,
        1792,   2048,   2304,   2560,   2816,   3072,   3328,   4096,   4608,
        5120,   6144,   6656,   8192,   9216,   10240,  12288,  13312,  16384,
        20480,  24576,  26624,  32768,  40960,  49152,  57344,  65536,  73728,
        81920,  90112,  98304,  106496, 114688, 122880, 131072, 139264, 147456,
        155648, 163840, 172032, 180224, 188416, 196608, 204800, 212992, 221184,
        229376, 237568, 245760, 253952, 262144};
};
```

SizaMap 提供了一张 Id 到 Size 的对应表，小对象在分配前都要先对齐到上一级大小

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

中间的 35 位构成 radix tree 的三级索引，分别是 12 / 12 / 11

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/tcmalloc-in-TOMA/page-and-span.jpeg)

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

+ mNext / mPrev 用于构建双向环形链表，链表头存放与 CentralFreeList 类型的数组中
+ mObjects 存储页内空闲对象列表
+ mNonFreeObjectNum 记录页内非空闲对象数
+ mLocation 记录页状态：使用中（拆分成小对象缓存或分配给应用程序）、缓存中、已归还给操作系统

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

+ mPagemap 记录着 PageId 与 Span 的对应关系（这将是我们找出所有 Span 的重要字段）
+ mPagemapCache 是 mPagemap 的缓存（我们不使用这个字段）
+ mLargeFree / mSmallFree 缓存未使用的 Span （分配出去的 Span 不由 PageHeap 管理，Span 指针在 mPagemap 中有记录）

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

+ mEmptySpan / mNonEmptySpan 分别存储所有对象未被使用的 Span 和有对象被使用的 Span
+ mUsedSlots 记录使用中 mTcSlots 的大小
+ mCacheSize 是 mUsedSlots 的上限
+ mMaxCacheSize 是 mCacheSize 的上限，它对于某一类对象而言是一个固定值

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

+ mMaxSize 是 mCacheSizeInByte 的上限？（这一条在实际使用 TOMA 时出现过反例）

# 标记 Obejct

## Overview

使用中的对象 = 所有 Span - PageHeap 缓存的 Span - Span 缓存的对象（即 CentralCache 中的对象） - ThreadCache 中的对象 - TCEntry 缓存的对象

我们需要设计两个类来存储所有对象的状态，方便标记及查找：

+ SpanManager 存储 SpanWrapper
+ SpanWrapper 存储当前 Span 内的对象的状态

## 辅助类

为方便分析程序的编写，TOMA 新增了一些辅助类

### SpanManager

```cpp
// This class must be very fast.
// Don't use any exception.
class SpanManager {
 private:
    using Leaf = std::array<observer_ptr<SpanWrapper>, kLeafLength>;
    constexpr static int rootLength = 1 << (kInteriorBits + kInteriorBits);
    using Root = std::array<std::unique_ptr<Leaf>, rootLength>;

 public:
    SpanManager(const CoredumpReader& coreReader,
                Address pageHeapAddr,
                Address centralCacheAddr,
                Address threadCacheAddr);
    SpanManager(const SpanManager& other) = delete;
    SpanManager(SpanManager&& other) = delete;
    SpanManager& operator=(const SpanManager& other) = delete;
    SpanManager& operator=(SpanManager&& other) = delete;

    void Run();

    SpanWrapper::iterator FindObj(Address addr);
    SpanWrapper::const_iterator FindObj(Address addr) const;

    std::set<std::unique_ptr<SpanWrapper>>& operator[](ClassId classId);

 private:
    void QueryGlobalSpan();
    void MarkFreeSpan(observer_ptr<SpanWrapper> sw);
    void MarkSpanCacheObjs(observer_ptr<SpanWrapper> sw);
    void QueryThreadFreeList();
    void QueryTcSlotObjs();

    observer_ptr<SpanWrapper> FindSpanWrapperByPageId(Address pageId) const;

 private:
    static SpanWrapper sEmptySpanWrapper;

 private:
    const CoredumpReader& mCoreReader;

    Address mPageHeapAddr;
    Address mCentralCacheAddr;
    Address mThreadCacheAddr;

    PageHeap mPageHeap;
    CentralCache mCentralCache;

    // It is used to search spans.
    Root mRoot;
    // It is used to iterate spans.
    std::array<std::set<std::unique_ptr<SpanWrapper>>, kNumClasses> mSpans;
};
```

+ `mSpans` 拥有 SpanWrapper 的所有权，并提供按照对象大小遍历 SpanWrapper 的能力
+ `mRoot` 是一棵 radix tree ，持有 SpanWrapper 的 observer ptr ，提供按照 PageId 搜索 SpanWrapper 的能力
+ `QueryGlobalSpan` / `MarkFreeSpan` / `MarkSpanCacheObjs` / `QueryThreadFreeList` / `QueryTcSlotObjs` 是寻找并标记 Object 的重要函数

总结：SpanManager 是 SpanWrapper 的拥有者和管理者，还是 Object 计算器

### SpanWrapper

```cpp
class SpanWrapper : public Span {
 public:
    template <typename T>
    struct Iter;

    template <typename T>
    class Object;

    template <typename T>
    struct Iter
        : public std::iterator<std::forward_iterator_tag,  // iterator_category
                               Object<T>,                  // value_type
                               std::size_t,                // difference_type
                               Object<T>*,                 // pointer
                               Object<T>>;                 // reference

 public:
    using iterator = Iter<SpanWrapper>;
    using const_iterator = Iter<const SpanWrapper>;

 public:
    explicit SpanWrapper(const Span& span);
    SpanWrapper(const SpanWrapper& other) = delete;
    SpanWrapper(SpanWrapper&& other) = delete;
    SpanWrapper& operator=(const SpanWrapper& other) = delete;
    SpanWrapper& operator=(SpanWrapper&& other) = delete;

    bool operator<(const SpanWrapper& other) const;

    iterator begin();
    iterator end();
    iterator find(Address addr);

    const_iterator begin() const;
    const_iterator end() const;
    const_iterator find(Address addr) const;

    std::size_t Size() const;

    bool IsFreeSpan() const;
    bool IsBigObj() const;
    std::size_t GetFreeObjectNum() const;
    std::size_t GetAllObjectNum() const;
    std::size_t Count(Tag tag) const;

 private:
    std::size_t GetIndex(Address addr) const;

 public:
    ClassSize mClassSize;
    Address mStartAddr;
    Address mEndAddr;

    std::vector<Tag> mObjTags;
};
```

关于 SpanWrapper ：

+ 从概念上说，SpanWrapper 是装着 Object 的容器
+ 从实现上说，SpanWrapper 仅仅记录 Object 的状态（`mObjTags` 数组），因为 Object 的起始地址可以从 `mObjTags` 的下标和 `mClassSize` 推断出来，Object 的大小就是 `mClassSize`
+ `GetIndex` 可以根据地址计算出 Object 相对于 Span 的偏移量（即地址属于 Span 的第几个对象）

关于 Object ：

+ 从概念上说，Object 应当记录对象的起始地址、大小和状态
+ 从实现上说，Object 只需要记录指向所属 SpanWrapper 的指针和 `mObjTags` 的下标，就可以计算出上述三个属性

总结：SpanWrapper 是 Object 的拥有者和管理者

## 寻找 Span

```cpp
void SpanManager::QueryGlobalSpan() {
    for (uint64_t pageId = 0; pageId < kPageIdLength;) {
        uint64_t nextPageId = 0;
        auto p = FindSpanByPageId(mCoreReader, mPageHeap, pageId, &nextPageId);
        if (p != nullptr) {
            Span span = mCoreReader.Defer<Span>(p);
            // Insert span to mSpans.
            // sw is observer ptr of span wrapper in mSpans.
            if (sw->IsFreeSpan()) {
                MarkFreeSpan(sw);
            } else {
                MarkSpanCacheObjs(sw);
            }
            // Insert observer ptr of span wrapper to mRoot.
            pageId += sw->mPageNum;
        } else {
            pageId = nextPageId;
        }
    }
}
```

QueryGlobalSpan 利用 PageMap3 来找出所有的 Span

注意：不要从 0 到 kPageIdLength 逐个遍历 PageId ，这样做非常慢

正确的做法是根据 radix tree 的特性，直接跳到下一个存在的 PageId

## 标记 PageHeap 缓存的 Span

```cpp
void SpanManager::MarkFreeSpan(observer_ptr<SpanWrapper> sw) {
    Assert(sw->mNonFreeObjectNum == 0);
    if (sw->mLocation == Span::eNormal) {
        for (auto it = sw->begin(); it != sw->end(); it++) {
            it->GetTag() = Tag::sNormalFreeSpan;
        }
    } else {
        for (auto it = sw->begin(); it != sw->end(); it++) {
            it->GetTag() = Tag::sReturnedFreeSpan;
        }
    }
}
```

被 PageHeap 缓存的 Span 可以通过 `mLocation` 字段识别出来

所谓标记，就是把 `mObjTags` 数组里的每一个元素都置为对应的状态

## 标记 CentralCache 缓存的对象

```cpp
void SpanManager::MarkSpanCacheObjs(observer_ptr<SpanWrapper> sw) {
    for (Address freeObj = reinterpret_cast<Address>(sw->mObjects);
         freeObj != 0;
         freeObj = mCoreReader.Defer<Address>(freeObj)) {
        auto it = sw->find(freeObj);
        it->GetTag() = Tag::sSpanCache;
    }
    auto freeObjectNum = sw->Count(Tag::sSpanCache);
    Assert(freeObjectNum == sw->GetFreeObjectNum());
}
```

## 标记 TCEntry 缓存的对象

```cpp
void SpanManager::QueryTcSlotObjs() {
    for (auto classId : range(kNumClasses)) {
        const CentralFreeList& centralFreeList = mCentralCache[classId];
        Assert(centralFreeList.mClassId == classId);
        // search tc slots
        auto usedSlot = centralFreeList.mUsedSlots;
        for (auto slotIndex : range(usedSlot)) {
            const TCEntry& entry = centralFreeList.mTcSlots[slotIndex];
            for (auto freeObj = entry.mHead; freeObj != entry.mTail;
                 freeObj = mCoreReader.Defer<void*>(freeObj)) {
                auto it = FindObj(reinterpret_cast<Address>(freeObj));
                Assert(it);
                it->GetTag() = Tag::sTcSlot;
            }
            auto it = FindObj(reinterpret_cast<Address>(entry.mTail));
            Assert(it);
            it->GetTag() = Tag::sTcSlot;
        }
    }
}
```

## 标记 ThreadCache 缓存的对象

```cpp
void SpanManager::QueryThreadFreeList() {
    TraverseDoubleLinkedList<ThreadCache, ThreadCacheIter, bool, false>(
        mCoreReader,
        mThreadCacheAddr,
        [this](const ThreadCache& threadCache, bool isHead) {
            const auto& freeList = threadCache.mFreeList;
            for (auto classId : range(kNumClasses)) {
                for (auto freeObj = freeList[classId].mObject;
                     freeObj != nullptr;
                     freeObj = mCoreReader.Defer<void*>(freeObj)) {
                    auto it = FindObj(reinterpret_cast<Address>(freeObj));
                    Assert(it);
                    it->GetTag() = Tag::sThreadCache;
                }
            }
            return true;
        });
}
```

# reference

1. [TCMalooc 解密](https://wallenwang.com/2018/11/tcmalloc/)

