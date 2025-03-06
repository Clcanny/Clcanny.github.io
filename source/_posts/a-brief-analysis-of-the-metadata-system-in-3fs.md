---
layout: post
title: a-brief-analysis-of-the-metadata-system-in-3fs
date: 2025-03-02 22:58:50
tags:
---

https://apple.github.io/foundationdb/developer-guide.html#how-foundationdb-detects-conflicts
serializability + external consistency
https://stackoverflow.com/questions/60365103/differences-between-strict-serializable-and-external-consistency
https://apple.github.io/foundationdb/developer-guide.html#snapshot-reads
Snapshot reads differ from ordinary (strictly serializable) reads by permitting the values they read to be modified by concurrent transactions, whereas strictly serializable reads cause conflicts in that case.
https://apple.github.io/foundationdb/developer-guide.html#conflict-ranges
Conflicts can be created, increasing isolation, by explicitly adding read or write conflict ranges.

versionstamps 机制
https://forums.foundationdb.org/t/implementing-versionstamps-in-bindings/250

basically, dirtree -> transaction
有哪些 table
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/common/kv/KeyPrefix-def.h#L6-L10
// Inode
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/meta/Schema.h#L361
key = id
common + asfile: https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/meta/Schema.h#L245
// Dentry
key = parent_id.name
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/meta/Schema.h#L410
https://www.kernel.org/doc/html/latest/filesystems/ext4/directory.html
There can be many directory entries across the filesystem that reference the same inode number -- these are known as hard links.
https://helgeklein.com/blog/hard-links-and-permissions-acls/
https://unix.stackexchange.com/questions/458558/how-do-hard-links-symbolic-links-and-acl-folder-permissions-interact
Why need dirAcl?
最大的用途是做 gc ？
https://askubuntu.com/questions/210741/why-are-hard-links-not-allowed-for-directories
directory hardlinks are not possible, so it acts as cache?
// Inode Session
INOS
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/store/FileSession.cc#L26
// User
user.uid -> UserAttr
// NodeTable
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/mgmtd/PersistentNodeInfo.h#L9
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/mgmtd/MgmtdTypes.h#L40
// MetaDistributor
大多数请求都是不按照 inode id 拆分的，有一些非常特殊的请求是按照 inode id 拆分的，比如 sync
拆分方式，按照 inode id 进行拆分，不是按照 subtree 进行拆分的
distributor 就是按照 inode id 分发请求的类
这张表存的是节点 versionstamp
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/store/ops/BatchOperation.h#L165-L168
setattr/create/close/sync 同时需要 batchoperaiton 来排队，和转发到同一台服务器
本质上是通过 batch 来提高吞吐
也只有这几个操作（对同一个文件）才有凑批的意义，其它操作凑批的意义很弱
比如对在同一个目录下新建很多个子文件，凑批了也没有节省很多资源

https://arxiv.org/html/2408.14158v1#S6.SS2.SSS3
Key Techinical Points of 3FS
Several meta services run concurrently to handle meta requests from clients.

https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/store/ops/BatchOperation.h#L35
BatchedOp 为什么会快？
file meta: https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/meta/Schema.h#L245
session?
就是因为对同一个文件的操作都凑批了，用同一个 transaction 处理完所有的请求
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/service/MetaOperator.cc#L116
https://github.com/deepseek-ai/3FS/blob/c3a16b5cd8caf7a604270813cc4a5a0772b3d279/src/meta/service/MetaOperator.h#L146
https://github.com/deepseek-ai/3FS/issues/84

3FS不cache obejcts的原因，会破坏fdb的lineariable read

3fs 如何回收超期文件？
SessionManager 用到的比较重要的类：
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/service/MetaServer.cc#L32
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/service/MetaServer.cc#L108
mgmtdClient_ = std::make_shared<::hf3fs::client::MgmtdClientForServer>(std::move(mgmtdClient));
prune session?
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/meta/components/SessionManager.cc#L274
prune session 是怎么产生的？
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/client/meta/MetaClient.cc#L590
https://github.com/deepseek-ai/3FS/blob/cd564a239a28cc51e55c1550099824b3d7903dd3/src/fbs/meta/Utils.h#L135
