---
layout: post
title: Enhancing Inode Attributes and Storage Policies in HDFS
date: 2024-08-27 00:59:08
categories:
  - [Computer Science, Big Data, HDFS]
---

## Background: HDFS Solutions and Implementation for Archival Storage

[Apache Hadoop 3.3.6 > Archival Storage, SSD & Memory](https://hadoop.apache.org/docs/stable/hadoop-project-dist/hadoop-hdfs/ArchivalStorage.html) introduces archival storage to decouple storage capacity from compute capacity:

> Archival Storage is a solution to decouple growing storage capacity from compute capacity. Nodes with higher density and less expensive storage with low compute power are becoming available and can be used as cold storage in the clusters. Based on policy the data from hot can be moved to the cold. Adding more nodes to the cold storage can grow the storage independent of the compute capacity in the cluster.

Archival storage consists of two key components:

1. Storage Policy Resolution: Determines the storage policy for files (e.g., hot, cold, warm, all SSD, one SSD).
2. Data Movement: Ensures data is relocated to match the storage policy, addressing any discrepancies between expected and actual storage locations.

[Apache Hadoop 3.3.6 > Archival Storage, SSD & Memory](https://hadoop.apache.org/docs/stable/hadoop-project-dist/hadoop-hdfs/ArchivalStorage.html) and [Storage-Policy-Satisfier-in-HDFS-Oct-26-2017.pdf](https://issues.apache.org/jira/browse/HDFS-10285) highlight two scenarios requiring data movement:

> 1. Setting a new storage policy on already existing file/dir will change the policy in Namespace, but it will not move the blocks physically across storage medias.
> 2. Other scenario is, when user rename the files from one affected storage policy file (inherited policy from parent directory) to another storage policy effected directory, it will not copy inherited storage policy from source. So it will take effect from destination file/dir parent storage policy. This rename operation is just a metadata change in Namenode. The physical blocks still remain with source storage policy.

Storage policy resolution is straightforward:

> The effective storage policy of a file or directory is resolved by the following rules.
>
> 1. If the file or directory is specified with a storage policy, return it.
> 2. For an unspecified file or directory, if it is the root directory, return the default storage policy. Otherwise, return its parent's effective storage policy.

Users have two options to move blocks according to a new policy. The first option is the [HDFS-10285: Storage Policy Satisfier in HDFS](https://issues.apache.org/jira/browse/HDFS-10285). The following figures illustrate the basic workflow of SPS:

![Fig-1: Namenode extensions](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/enhancing-inode-attributes-and-storage-policies-in-hdfs/fig-1-namenode-extensions.png)

![Fig-2: Coordinatingblocksmovement using C-DN](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/enhancing-inode-attributes-and-storage-policies-in-hdfs/fig-2-coordinating-blocks-movement-using-c-dn.png)

The primary responsibility of the NameNode extensions is to recursively scan all files within a user-specified directory and connect with the Coordinator DataNode using the `BlockStorageMovementCommand`. The details are illustrated in [Storage-Policy-Satisfier-in-HDFS-Oct-26-2017.pdf](https://issues.apache.org/jira/browse/HDFS-10285):

> If the source path is a directory then all the files under the directory recursively would be considered for satisfying the policy. All the submitted directory inodes will be tracked separately at queue `BlockStorageMovementNeeded#spsDirsToBeTraversedLater`, these directories will be asynchronously traversed and all the file inodes under each directory will be added to the queue `BlockStorageMovementNeeded#storageMovementNeeded`. There could be a case of large directory, which can have several files under it. Here, traversing all files and collecting Inodes would be time consuming and its not recommended to hold Namenode locks longer time until the directory is fully scanned. Again, this could increase memory consumption if we keep lot of files inode into memory. To avoid these issues, SPS will throttle itself and traverse the directories in batch wise. Added a limit of 1000 size to the queue `storageMovementNeeded`. If `storageMovementNeeded` becomes full with 1000 elements, directory traversal will be suspended until `storageMovementNeeded` has some free slots available, lower than 1000. When scan was suspended, it releases the Namenode lock, so that other Namenode operations will not be blocked.

## Limitations in Storage Policy Resolution and Improvements

In HDFS, the biggest shortcoming of storage policy resolution is its counter-intuitive nature. Consider this example, where txid (transaction ID) represents the logical clock for capturing "happen-before" relationships - transactions with smaller txid values occur before those with larger ones:

+ Operations:
  + [TxID=1] Set storage policy to "hot" on directory /a/b.
  + [TxID=2] Set storage policy to "all ssd" on directory /a.
+ Result: The file /a/b/c unexpectedly retains the "hot" storage policy, even when the policy for the entire /a directory is reset. Let's take the Linux `chown` command as an example. In Linux, if a user executes `chown -R` on /a, it may not affect /a/b/c if `chown -R` was previously executed on /a/b. This behavior can seem unexpected and counter-intuitive.

## Proposing Enhancements for Metadata and Replica Movement
