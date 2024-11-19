---
layout: post
title: "Design Document: Using Standard MVCC to Implement HDFS Snapshots"
date: 2024-11-06 00:16:40
categories:
  - [Computer Science, Big Data, DFS]
---

In this blog, we will explore how using a standard MVCC mechanism can improve the implementation of HDFS snapshots compared to the original HDFS approach. Adopting standard MVCC brings several architectural advantages:

+ Clearer Software Layering: One of the key advantages of using MVCC is the **clear separation of concerns between the version control logic and the core file system structures (like the directory tree)**. This separation leads to a more modular design, simplifying both the implementation and future optimizations.
  + Optimizations like Serializable Snapshot Isolation, which are used in PostgreSQL, can be implemented more easily within a dedicated MVCC layer.
  + The separation also allows us to apply theoretical frameworks, such as the theorem described in [Weak Consistency: A Generalized Theory and Optimistic Implementations for Distributed Transactions](https://pmg.csail.mit.edu/papers/adya-phd.pdf), to **formally prove the correctness of this MVCC layer**.
+ Reduced Complexity: Implementing snapshots using a more common method like MVCC lowers the learning curve and reduces the cognitive burden on developers and maintainers, as the approach is widely understood and used in various systems.
+ Minimal Performance Overhead: While there is some performance cost associated with using MVCC, it is lightweight and acceptable when compared to the benefits it brings in terms of clarity and maintainability.

## Existing Approaches of Snapshot

Snapshotting directories such as tmp may be very expensive given the rate at which they change.

It is easier implement managing snapshot locally along with the namespace, with no need for distributed co-ordination.

[HDFS Snapshots Design (HDFS-2802 Attachment)](https://issues.apache.org/jira/secure/attachment/12551674/snapshot-design.pdf)

[Snapshots](https://issues.apache.org/jira/secure/attachment/12581376/Snapshots20120429.pdf)

This is not a major burden, however.As mentioned earlier, we only have to do this when there
is an older, snapshotted copy of the inode.

snapshot 怎么应对分布式架构？
pg 和 mysql 都可以开启默认 mvcc ，为什么 hdfs 不可以？
为什么 snapshot 和 mvcc 这么割裂？snapshot 完全是一套自己的方案，不能复用 mvcc 带来的性能优势？
重新写一篇文档，把各家的做法串进来？

```java
+  public void createSnapshot(final String path, final String snapshotName
+      ) throws IOException {
+    // Find the source root directory path where the snapshot is taken.
+    final INodesInPath i = fsdir.getINodesInPath4Write(path);
+    final INodeDirectorySnapshottable srcRoot
+        = INodeDirectorySnapshottable.valueOf(i.getLastINode(), path);
+
+    fsdir.verifyMaxComponentLength(snapshotName, path, 0);
+    srcRoot.addSnapshot(snapshotCounter, snapshotName);
+      
+    //create success, update id
+    snapshotCounter++;
+    numSnapshots.getAndIncrement();
+  }
```

https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/FSDirectory.java#L1394

```java
  public INodesInPath addLastINode(INodesInPath existing, INode inode,
      FsPermission modes, boolean checkQuota, Optional<QuotaCounts> quotaCount)
      throws QuotaExceededException {
    final boolean added = parent.addChild(inode, true,
        existing.getLatestSnapshotId());
    return INodesInPath.append(existing, inode, inode.getLocalNameBytes());
  }

  /**
   * Add a child inode to the directory.
   * 
   * @param node INode to insert
   * @param setModTime set modification time for the parent node
   *                   not needed when replaying the addition and 
   *                   the parent already has the proper mod time
   * @return false if the child with this name already exists; 
   *         otherwise, return true;
   */
  public boolean addChild(INode node, final boolean setModTime,
      final int latestSnapshotId) {
    final int low = searchChildren(node.getLocalNameBytes());
    if (low >= 0) {
      return false;
    }

    if (isInLatestSnapshot(latestSnapshotId)) {
      // create snapshot feature if necessary
      DirectoryWithSnapshotFeature sf = this.getDirectoryWithSnapshotFeature();
      if (sf == null) {
        sf = this.addSnapshotFeature(null);
      }
      return sf.addChild(this, node, setModTime, latestSnapshotId);
    }
    addChild(node, low);
    if (setModTime) {
      // update modification time of the parent directory
      updateModificationTime(node.getModificationTime(), latestSnapshotId);
    }
    return true;
  }
```

```java
  /**
   * For snapshot paths, it is the id of the snapshot; or 
   * {@link Snapshot#CURRENT_STATE_ID} if the snapshot does not exist. For 
   * non-snapshot paths, it is the id of the latest snapshot found in the path;
   * or {@link Snapshot#CURRENT_STATE_ID} if no snapshot is found.
   */
  private final int snapshotId;
```

https://hadoop.apache.org/docs/r2.8.2/hadoop-project-dist/hadoop-hdfs/api/org/apache/hadoop/hdfs/server/namenode/INodeReference.html
https://hadoop.apache.org/docs/r3.4.1/hadoop-project-dist/hadoop-hdfs/build/source/hadoop-hdfs-project/hadoop-hdfs/target/api/org/apache/hadoop/hdfs/server/namenode/INodeReference.html

[Snapshotting in Hadoop Distributed File System for Hadoop Open Platform as Service](https://web.tecnico.ulisboa.pt/~ist14191/repository/Summary.pdf)

[Snapshots in Hadoop Distributed File System](https://sameeragarwal.github.io/hdfs_snapshots_ucb_tr.pdf)
