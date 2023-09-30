---
layout: post
title: An Introductory Guide to LSM Tree Storage Engines - LevelDB and RocksDB
date: 2023-10-01 12:00:00
categories:
  - [Computer Science, Storage Engine]
---

## Overview

The paper [Optimizing Space Amplification in RocksDB](https://www.cidrdb.org/cidr2017/papers/p82-dong-cidr17.pdf) provides an insightful background on Log-Structured Merge Trees (LSM trees) in the section titled "LSM-TREE BACKGROUND":

> Whenever data is written to the LSM-tree, it is added to an in-memory write buffer called mem-table, implemented as a skiplist having O(log(n)) inserts and searches. At the same time, the data is appended to a Write Ahead Log (WAL) for recovery purposes. After a write, if the size of the mem-table reaches a predetermined size, then (i) the current WAL and mem-table become immutable, and a new WAL and mem-table are allocated for capturing subsequent writes, (ii) the contents of the mem-table are flushed out to a "Sorted Sequence Table" (SST) data file, and upon completion, (iii) the WAL and mem-table containing the data just flushed are discarded.
>
> Each of the SSTs stores data in sorted order, divided into unaligned 16KB blocks (when uncompressed). Each SST also has an **index block** for binary search with one key per SST block. SSTs are organized into a sequence of levels of increasing size, Level-0 – Level-N, where each level will have multiple SSTs, as depicted in Figure 1. Level-0 is treated specially in that its SSTs may have **overlapping** key ranges, while the SSTs of higher levels have distinct non-overlapping key ranges. When the number of files in Level-0 exceeds a threshold (e.g., 4), then the Level-0 SSTs are merged with the Level-1 SSTs that have overlapping key ranges; when completed, all of the merge sort input (L0 and L1) files are deleted and replaced by new (merged) L1 files. For L>0, when the combined size of all SSTs in level-L exceeds a threshold (e.g., 10^(L−1)(GB)) then one or more level-L SSTs are selected and merged with the overlapping SSTs in level-(L+1), after which the merged level-L and level-(L+1) SSTs are removed.
>
> The search for a key occurs at each successive level until the key is found or it is determined that the key is not present in the last level. It begins by searching all mem-tables, followed by all Level-0 SSTs and then the SST’s at the next following levels. At each of these successive levels, three binary searches are necessary. The first search locates the target SST by using the data in the Manifest File. The second search locates the target data block within the SST file by using the SST's index block. The final search looks for the key within the data block. **Bloom filters** (kept in files but cached in memory) are used to eliminate unnecessary SST searches, so that in the common case only 1 data block needs to be read from disk. Moreover, recently read SST blocks are cached in a block cache maintained by RocksDB and the operating system’s page cache, so access to recently fetched data need not result in I/O operations.
>
> Range queries are more involved and always require a search through all levels since all keys that fall within the range must be located. First the mem-table is searched for keys within the range, then all Level-0 SSTs, followed by all subsequent levels, while disregarding duplicate keys within the range from lower levels. **Prefix Bloom filters** can reduce the number of SSTs that need to be searched.

![Optimizing Space Amplification in RocksDB - Figure 1](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/an-introductory-guide-to-lsm-tree-storage-engines-leveldb-and-rocksdb/optimizing-space-amplification-in%20rocksdb-figure-1.png)

![Optimizing Space Amplification in RocksDB - Figure 2](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/an-introductory-guide-to-lsm-tree-storage-engines-leveldb-and-rocksdb/optimizing-space-amplification-in%20rocksdb-figure-2.png)

## Compaction Core: The Merge Phase of the Merge Sort Algorithm

Given that the SSTables are sorted, the compaction process mirrors the merge phase of the merge sort algorithm. The [`VersionSet::MakeInputIterator`](https://github.com/google/leveldb/blob/main/db/version_set.cc#L1219) function prepares arrays of `Iterator` for the SSTables involved in compaction, which are then passed to [`NewMergingIterator`](https://github.com/google/leveldb/blob/main/table/merger.cc#L179) to form a composite `MergingIterator`. The [`FindSmallest`](https://github.com/google/leveldb/blob/main/table/merger.cc#L148) function within this composite `MergingIterator` is straightforward: it compares all the subsequent elements of the internal iterators to find the smallest next element. By leveraging the `MergingIterator`, the [`DBImpl::DoCompactionWork`](https://github.com/google/leveldb/blob/068d5ee1a3ac40dabd00d211d5013af44be55bea/db/db_impl.cc#L892) function is capable of performing compaction by iterating through all elements from smallest to largest, subsequently outputting the results to a new SSTable.

## Scheduler

## 分离 Key & Value

# 每一层 Size & 文件数 & 放大倍数

# 深度

# 为什么需要一个文件包含多个 Block ?

# 不可能三角

# Bloom Filter & Perfix Bloom Filter

## Reference

+ [Optimizing Space Amplification in RocksDB](https://www.cidrdb.org/cidr2017/papers/p82-dong-cidr17.pdf)
