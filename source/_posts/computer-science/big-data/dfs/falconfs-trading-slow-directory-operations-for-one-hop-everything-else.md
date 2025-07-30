---
layout: post
title: falconfs-trading-slow-directory-operations-for-one-hop-everything-else
date: 2025-07-30 23:49:00
categories:
  - [Computer Science, Big Data, DFS]
---

## Core Idea

FalconFS represents a paradigm shift in distributed file system design by making deliberate tradeoffs optimized for AI workloads. Unlike traditional distributed file systems that aim for balanced performance across all operations, FalconFS strategically sacrifices scalability and performance on complex write requests to dramatically boost scalability and performance on read requests and simple write requests - the dominant operations in deep learning pipelines.

## Introduction: The FalconFS Architecture

FalconFS consists of three main components:

+ MNodes: Handle metadata
+ File Stores: Handle data storage
+ Clients

The key innovation lies in how metadata is partitioned. Both dentries and inodes are assigned to **owner MNodes** based on filename hashing - without including parent directory IDs. Dentries are replicated across all MNodes through lazy replication. This design allows any MNode to resolve full paths locally.

![Figure 5: Architecture of FalconFS](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/falconfs-trading-slow-directory-operations-for-one-hop-everything-else/figure-5-architecture-of-falconfs.png)

![Table 1: Scheme of FalconFS's metadata](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/falconfs-trading-slow-directory-operations-for-one-hop-everything-else/table-1-scheme-of-falconfs-s-metadata.png)

## Boosting Read Performance and Scalability

FalconFS achieves exceptional read performance through its one-hop architecture.

### Performance

When a client needs to access `/data1/image.jpg`, it hashes the filename `image.jpg` to determine the target MNode. That MNode can complete the entire operation locally because:

+ It owns the inode for `image.jpg`.
+ It has replicated dentries for all ancestor directories (`/`, `data1`).

This eliminates the request amplification problem where traditional DFS clients must look up each path component separately, potentially requiring multiple network round-trips.

### Scalability

The filename-based partitioning ensures that as long as filenames are reasonably distributed (which is typical in AI datasets with millions of unique files), requests naturally load-balance across MNodes. Adding more MNodes directly increases the system's capacity to handle concurrent requests, providing near-linear scalability for read operations.

## Maintaining Correctness Guarantees

FalconFS ensures correctness through careful design of its concurrency control mechanisms, providing serializability, linearizability, and atomicity guarantees.

### Serializability and Linearizability

FalconFS employs a sophisticated two-level locking protocol based on two-phase locking:

+ **Coordinator-level implicit locks**: MSI-style (Modified-Shared-Invalid) coherence protocol
+ **MNode-level explicit locks**: Traditional in-memory locks (e.g., `std::shared_lock`)

The locking order is strictly enforced from root to leaf to prevent deadlocks. For an operation on `/data1/image.jpg`, the process is as follows: First, the coordinator locks `/`, `data1` and `image.jpg`. Then the MNode locks `/`, `data1` and `image.jpg`. Locks are always released in the reverse order once the operation is complete.

The 2PL protocol guarantees **serializability** and **linearizability**. Linearizability is guaranteed because:

+ The linearization point for each request is clearly defined as the moment it acquires its final lock, either at the MNode or the coordinator.
+ TThis lock acquisition always occurs within the request's real-time bounds - after the client initiates the operation and before any response is returned.
+ The 2PL protocol enforces a consistent ordering of conflicting operations. Once a request acquires its locks, no conflicting request can proceed until those locks are released. This ensures a globally consistent total order that respects the partial orderings of conflicting requests.

### Atomicity

FalconFS handles atomicity differently based on operation complexity:

+ Inode Creation: These operations only modify a single inode and dentry on the same MNode. The owning MNode handles atomicity internally through local transactions, without coordination overhead.
+ Other Write Requests: Operations requiring atomicity across multiple MNodes are coordinated via a centralized coordinator using the 2PC protocol.

## MSI Protocol for Dentry Management

To achieve one-hop processing, clients do not request the coordinator to explicitly take locks. Instead, coordinator-level locks are implemented using a memory coherence protocol - similar to the MSI model.

+ Normally, the owner MNode shares or replicates its dentry with other MNodes. The dentry is in the **S (Shared)** state, meaning all MNodes can read it, but no modifications (even by the owner) are allowed.
+ When the owner MNode needs to modify the dentry (e.g., for removal, permission changes, or renaming), the coordinator revokes all S states from other MNodes, transitions them to **I (Invalid)**, and grants **M (Modified)** state to the owner.

Once all MNode-level locks are acquired, the MNode must verify that all cached dentry states remain valid. Additionally, the MNode blocks any invalidation requests from the coordinator until the locks are released.

Since there is no explicit acquisition of coordinator-level locks by the client, the locking mechanism is referred to as implicit locks. This design leverages the coherence protocol to ensure consistency and eliminate the need for explicit lock management at the coordinator level.
