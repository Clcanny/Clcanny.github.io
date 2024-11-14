---
layout: post
title: hdfs-snapshots-demystified-how-and-why-it-works
date: 2024-11-14 22:12:59
categories:
  - [Computer Science, Big Data, DFS]
math: true
---

### Step 1: Using Undo Logs to Implement Snapshots

In HDFS, the NameNode uses edit logs to record every operation that modifies the file system (such as mkdir, delete, or rename). These logs are essential because they capture the sequence of changes, which allows the system to reconstruct the current state by replaying the logs from a known checkpoint.

While HDFS doesn't natively maintain undo logs, I find it helpful to think about a conceptual form of "reverted edit logs" - what I call undo logs. These would represent the reverse of the changes recorded in the edit logs, essentially allowing us to "undo" past operations.

If we imagine having access to undo logs alongside the current state of the file system, it's possible to think about how we could reconstruct past states by applying these "reverted" operations. With a complete set of undo logs, we could theoretically rewind the file system to any previous point in time.

This way of thinking shows how we could reconstruct any state in the file system's history from the current state, without needing to store the entire file system at each point. It's a useful mental model, even though it's not how HDFS snapshots are actually implemented.

#### An Example to Illustrate the Concept

![An Example of Replaying Undo Logs](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/hdfs-snapshots-demystified-how-and-why-it-works/an-example-of-replaying-undo-logs.excalidraw.png)

There are a few key points to notice in the graph above:

+ For simplicity, the **rename** operation is represented as a combination of a **delete** and **create** operation. For example, in the edit logs, the operation rename /a/b to /a/c is shown as two operations: delete /a/b followed by create /a/c. This is not how HDFS actually implements rename operations in its edit logs, but the change is made here to better illustrate how and why snapshots works.
+ The undo log for a **delete /a** operation is not just create /a, but **create /a and its entire subtree**. Conceptually, when a user deletes /a, the edit log records **delete /a and its subtree**. The shortened form delete /a is simply an abbreviation, making it easier for the edit logs to record. Therefore, the corresponding undo log typically involves **create /a and its subtree** to fully restore the deleted structure.

#### Why Replaying Undo Logs Is the Right Approach

If we design undo logs that precisely match each corresponding edit log (this means that every operation recorded in the edit logs can be effectively reversed by applying its matching undo log), it becomes possible to revert the file system to any previous point in time. Since every change in the file system can be undone in this way, it naturally follows that using this approach to implement snapshots is correct.

### Step 2: Attaching Undo Logs to the Parent Inode

In this step, we attach the undo logs to the parent inode of the operated inode. By associating the undo logs with the parent inode, we can efficiently filter out irrelevant undo logs when users request a specific subtree of a snapshot rather than the entire directory tree.

#### How Undo Logs Are Organized

![An Example of Attaching Undo Logs to Parent Inodes](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/hdfs-snapshots-demystified-how-and-why-it-works/an-example-of-attaching-undo-logs-to-parent-inodes.excalidraw.png)

The above example demonstrates how undo logs are **attached** to the **parent inode** of the inode being operated on by the undo log. This ensures that the undo logs are localized to the relevant subtree, allowing for efficient restoration of snapshots:

+ The operation described by undo log 4 is on /a. In the current snapshot, the parent of /a is root, so undo log 4 is attached to root.
+ The operation described by undo log 3 is on /a/c. Even though /a is not present in the current snapshot, undo log 3 is still attached to /a. This is acceptable since the undo logs track changes over time, including inodes that may no longer exist in the current snapshot.

Notice that there is a dashed line from root to /a in the graph. This dashed line indicates that /a and its subtree are preserved as part of undo log 4, but /a is not visible in the current snapshot. In other words, while /a is not part of the active directory structure in the snapshot, it still exists "behind the scenes" and will be restored when the undo log is applied.

#### How Undo Logs Are Applied

Here is an example used to discuss how irrelevant undo logs are filtered out during the application process below. The edit logs are as follows:

1. Create /a.
2. Create /a/b.
3. Delete /a/b and create /a/c: This represents a rename operation, where /a/b is renamed to /a/c. A rename operation is treated as a combination of a delete operation (deleting /a/b) and a create operation (creating /a/c).
4. Delete /a.
5. Create /d.
6. Something related to /d's subtree.
7. Something related to /d's subtree.
8. Create /e.
9. Something related to /e's subtree.
10. Something related to /e's subtree.
11. Delete /e.

The corresponding undo logs are displayed in the graph below:

![An Example of Filtering Irrelevant Undo Logs](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/hdfs-snapshots-demystified-how-and-why-it-works/an-example-of-filtering-irrelevant-undo-logs.excalidraw.png)

When a user attempts to access **/a** at a specific point in time, the process of applying undo logs is straightforward, as shown in the graph below:

+ Step I:
  + In the **current snapshot**, the directory tree consists of **inode root** and **inode /d**.
  + Since /d is neither an ancestor nor a descendant of /a, /d and any undo logs attached to it are ignored.
  + Among the undo logs attached to root, logs 11, 8, and 5 are unrelated to /a and are therefore ignored as well.
  + The **most recent relevant undo log** is edit log 4 (colored yellow). This log is applied to revert the system to a previous state, resulting in snapshot s3.
+ Step II:
  + In **snapshot s3**, the directory tree now includes root, /a, and /b. Although inode /d is still present in the tree, it is colored gray, indicating that it is being ignored (no further action is taken on it).
  + Among the remaining undo logs, the **most recent one** is edit log 3 (also colored yellow). This log is applied, further reverting the system.
+ Repeat the process of finding the next relevant undo log within each newly applied snapshot until either: reach the point in time specified by the user, or run out of relevant undo logs related to the specified subtree.

![Illustration of Applying Undo Logs for Accessing /a](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/hdfs-snapshots-demystified-how-and-why-it-works/illustration-of-applying-undo-logs-for-accessing-a.excalidraw.png)

While applying the logs, the system determines that the undo logs colored **green** are **relevant** to the restoration of /a because they involve operations on **/a, its ancestors, or its descendants**. The undo logs colored **gray** are irrelevant because they involve operations on other parts of the file system and do not affect **/a, its ancestors, or its descendants**.

#### Why Filtering Some Undo Logs Does Not Affect Correctness

+ If the user only creates or deletes inodes, filtering out undo logs that are not related to the user's requested subtree is correct.
+ But why can a rename operation be viewed as a combination of a delete and a create operation without affecting the snapshot? The reason is that a rename operation acts as a **split point** in the history of the file system. Specifically:
  + The history (edit logs) before the rename is only relevant when the user is accessing the source path. This history becomes irrelevant when accessing the destination path. For example, consider the following edit logs: create /a, create /a/b, create /a/b/c, delete /a/b/c, and rename /a/b to /d/e. **The history of /a/b (and its subtree) before the rename is irrelevant to /d/e**. In other words, **/d/e/c never existed at any point in time**.
  + Similarly, the history (edit logs) after the rename is only relevant when accessing the destination path, and is irrelevant to the source path. For example, consider the following edit logs: create /a, create /a/b, rename /a/b to /d/e, create /d/e/f, and delete /d/e/f. The history of /d/e (and its subtree) after the rename is irrelevant to /a/b. In other words, /a/b/f never existed at any point in time, and the operations on /d/e after the rename do not affect the state of /a/b before the rename.
  + Thus, treating a rename as a delete operation (from the source path) and a create operation (for the destination path) is valid. The histories (edit logs) before the rename, along with the delete log, belong to the source path, while the histories after the rename, along with the create log, belong to the destination path. In short, **these two parts of the history are completely independent and do not need to be aware of each other**.

### Step 3. Constraint on Accessing Snapshots and Related Optimization

In HDFS, users can only access specific points in time where a snapshot has been explicitly created. This introduces an important constraint: before accessing a point in time, the user must first issue the `createSnapshot` command, and only the system state at the moment the snapshot is created can be accessed. This means **users cannot access arbitrary points in time** - only those corresponding to completed snapshots.

This constraint allows for an optimization in how undo logs are handled.

#### How Undo Logs Are Offset

Undo logs can be offset when their effects cancel each other out, and no snapshot depends on the intermediate states between them. The key idea behind offsetting is simple: if two undo logs have converse effects (e.g., one log creates an inode and another deletes it) and no snapshot captures the system's intermediate state between these two operations, they can be safely ignored. This optimization reduces the overhead of applying unnecessary undo logs when restoring a snapshot.

Let's consider an example:

+ The user takes snapshot s0.
+ Afterward, the user creates /a.
+ (No snapshot is taken.)
+ A series of operations related to /a occur.
+ (No snapshot is taken.)
+ Finally, the user deletes /a.
+ The user takes snapshot s3.

In the example above, the undo logs related to /a between snapshot s0 and snapshot s3 can be offset. This is because:

+ The creation of /a, followed by its deletion, produces converse effects,
+ Since no snapshot was taken during the intermediate steps, the system does not need to retain the intermediate states of /a.

#### Data Structure Used to Offset Undo Logs: `Diff`

[HDFS](https://github.com/apache/hadoop/tree/96572764921706b1fecaf064490457d36d73ea6e) uses the [`ChildrenDiff`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/snapshot/DirectoryWithSnapshotFeature.java#L48) data structure, which extends [`Diff`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/util/Diff.java#L75), to manage undo logs between snapshots. `Diff` is responsible for recording changes (such as creations and deletions) that occur after each snapshot, and it plays a critical role in offsetting undo logs.

Each `Diff` is associated with a specific snapshot and maintains two lists:

+ Created List: This list records all newly created children **after** the snapshot.
+ Deleted List: This list tracks the children that were deleted **after** the snapshot.

Maintaining a `Diff` is straightforward:

+ When an edit log creates a new inode, the inode is added to the created list in the `Diff` of the **latest** snapshot.
+ When an edit log deletes an inode:
  + If the inode is already in the created list of the **latest** snapshot, it is removed from the created list.
  + If the inode is not in the created list of the **latest** snapshot, it is added to the deleted list.
+ Notice the following special case: When a user creates snapshot $s_0$, then deletes /a, and finally recreates /a, with no snapshots taken between these two edit logs (meaning they belong to the same `Diff` of $s_0$), the resulting `Diff` for $s_0$ will have a created list of {a} and a deleted list of {a}.

![An Example of Offsetting Undo Logs](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/hdfs-snapshots-demystified-how-and-why-it-works/an-example-of-offsetting-undo-logs.excalidraw.png)

Now, using the above graph as an example (note that each grid is generated by first applying the edit log, followed by taking a snapshot, if necessary):

+ In the scenario where all snapshots are taken, every change made to the file system is captured in the `Diff` structures between snapshots. Each undo log is recorded in the `Diff` of the corresponding snapshot. No undo logs can be offset. This behavior effectively reverts to the approach described in **Step 2**, where undo logs are attached to the parent inode and applied recursively **without any possibility of offsetting**.
+ In the scenario where only snapshot s0 and snapshot s4 are taken:
  + When delete /a occurs, snapshot s0 is the latest snapshot. As a result, /a is removed from the created list in the `Diff` of snapshot s0.
  + Similarly, when delete /b occurs, snapshot s0 is still the latest snapshot. Therefore, /b is also removed from the created list in the `Diff` of snapshot s0.
  + In this scenario, the creation and subsequent deletion of /a and /b cancel each other out, and the two undo logs are offset.

A more detailed set of rules for maintaining `Diff` is provided [here](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/util/Diff.java#L36-L69) (while the detailed rules may seem a bit verbose, the concept is easier to grasp using the offset idea - in my opinion, the offset approach offers a clearer understanding, lol):

```java
/**
 * Two lists are maintained in the algorithm:
 * - c-list for newly created elements
 * - d-list for the deleted elements
 *
 * Denote the state of an element by the following
 *   (0, 0): neither in c-list nor d-list
 *   (c, 0): in c-list but not in d-list
 *   (0, d): in d-list but not in c-list
 *   (c, d): in both c-list and d-list
 *
 * For each case below, ( , ) at the end shows the result state of the element.
 * Case 1. Suppose the element i is NOT in the previous state.             (0, 0)
 *   1.1. create i in current: add it to c-list                            (c, 0)
 *     1.1.1. create i in current and then create: impossible
 *     1.1.2. create i in current and then delete: remove it from c-list   (0, 0)
 *     1.1.3. create i in current and then modify: replace it in c-list    (c', 0)
 *   1.2. delete i from current: impossible
 *   1.3. modify i in current: impossible
 * Case 2. Suppose the element i is ALREADY in the previous state.         (0, 0)
 *   2.1. create i in current: impossible
 *   2.2. delete i from current: add it to d-list                          (0, d)
 *     2.2.1. delete i from current and then create: add it to c-list      (c, d)
 *     2.2.2. delete i from current and then delete: impossible
 *     2.2.2. delete i from current and then modify: impossible
 *   2.3. modify i in current: put it in both c-list and d-list            (c, d)
 *     2.3.1. modify i in current and then create: impossible
 *     2.3.2. modify i in current and then delete: remove it from c-list   (0, d)
 *     2.3.3. modify i in current and then modify: replace it in c-list    (c', d)
 */
```

#### Defining INode Visibility Using `Diff`

Consider an inode n:

+ If n appears in the created list of the `Diff` for snapshot $S_{created}$, it means that n was created **after** $S_{created}$.
+ If n appears in the deleted list of the `Diff` for snapshot $S_{deleted}$, it means that n was deleted **after** $S_{deleted}$.

Given this, the inode **n** is **visible** in the range **$(S_{created}, S_{deleted}]$**.

Consider the example in "An Example of Offsetting Undo Logs". In the scenario where all snapshots are taken, /a appears in the created list of the `Diff` for snapshot s0 and in the deleted list of the `Diff` for snapshot s2. This means /a is visible in the range $(s_0, s_2]$, so /a is present and visible in both snapshot s1 and snapshot s2.

#### Why Offsetting Undo Logs Using `Diff` Is the Right Approach

This question can be broken down into two sub-questions:

##### Why the Offset Idea Works

The offset concept works because if two undo logs either **cancel each other out** (e.g., creation followed by deletion) or **overwrite one another** (e.g., creation followed by modification), and the intermediate directory tree is not needed by any snapshot, it can safely be ignored.

##### Why Erasing the Order of Undo Logs Within the Same `Diff` Is Okay

In Step 3, compared to Step 2, the index of each undo log is erased, and all undo logs within the same `Diff` lose their explicit operation order. Why is this acceptable?

The reason is straightforward: if two undo logs are unrelated (e.g., creating /a and creating /b), their operation order doesn't matter. Since no snapshot is taken between these operations, their happens-before relationship is useless.

On the other hand, if the undo logs are related (e.g., a creation followed by a deletion of the same inode), they effectively offset each other. For example:

+ If an inode is created and then deleted, it will no longer appear in either the created or deleted lists.
+ If an inode is deleted and then recreated, it will appear in both the deleted and created lists. This is the only scenario that can lead to this outcome, so when we observe two same-name inodes in both the deleted and created lists within the same `Diff`, we know that they were first deleted and then recreated. This is the only case where the order of two edit logs matters, but we can still infer their order from the lists.
+ If an inode is created and then modified, the modified inode will be recorded in the created list.

In all cases, the final state in the `Diff` is what matters, and the system can safely disregard the specific order of operations as long as no snapshots capture the intermediate states.

### Step 4: nvestigating How HDFS Implements Snapshot Optimization - Filtering and Offsetting Undo Logs

In this step, we will explore how the HDFS implementation supports the ideas behind Step 1, Step 2 and Step 3. Specifically, we will look at how HDFS:

+ Step 1: Treats a rename operation as a combination of a deletion and a creation operation.
+ Step 2: Filters out irrelevant undo logs by leveraging the directory tree structure, ensuring that only necessary changes are tracked and applied.
+ Step 3: Uses `Diff` objects to offset undo logs, optimizing storage by canceling or overwriting operations when they no longer affect the file system state in meaningful ways.

1. 算 latest snpashot id
2. Inode reference & 区分事件
3. 追踪一下 rename

#### How HDFS Filters and Offsets Undo Logs in `DirectoryDiff::getChild`

In this section, we will explore how HDFS implements the ideas behind Step 2 and Step 3 through the code in `DirectoryDiff::getChild`. We will focus on the following key pieces of code that demonstrate these steps in action.

First, the relevant part of [`INodesInPath::resolve`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/INodesInPath.java#L223-L225) calls `INodeDirectory::getChild`:

```java
// normal case, and also for resolving file/dir under snapshot root
curNode = dir.getChild(childName,
    isSnapshot ? snapshotId : CURRENT_STATE_ID);
```

This leads to [`DirectoryDiff::getChild`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/snapshot/DirectoryWithSnapshotFeature.java#L241), which is central to understanding how undo logs are filtered and offset. Here's the core snippet from `DirectoryDiff::getChild`:

```java
/** @return the child with the given name. */
INode getChild(byte[] name, boolean checkPosterior,
    INodeDirectory currentDir) {
  for(DirectoryDiff d = this; ; d = d.getPosterior()) {
    final Container<INode> returned = d.diff.accessPrevious(name);
    if (returned != null) {
      // the diff is able to determine the inode
      return returned.getElement();
    } else if (!checkPosterior) {
      // Since checkPosterior is false, return null, i.e. not found.
      return null;
    } else if (d.getPosterior() == null) {
      // no more posterior diff, get from current inode.
      return currentDir.getChild(name, Snapshot.CURRENT_STATE_ID);
    }
  }
}
```

`DirectoryDiff::getChild` calls [`Diff::accessPrevious`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/util/Diff.java#L369-L394), which plays a crucial role in the process. Below is the relevant code snippet:

```java
/**
 * @return null if the element cannot be determined in the previous state
 *         since no change is recorded and it should be determined in the
 *         current state; otherwise, return a {@link Container} containing the
 *         element in the previous state. Note that the element can possibly
 *         be null which means that the element is not found in the previous
 *         state.
 */
private static <K, E extends Diff.Element<K>> Container<E> accessPrevious(
    final K name, final List<E> clist, final List<E> dlist) {
  final int d = search(dlist, name);
  if (d >= 0) {
    // the element was in previous and was once deleted in current.
    return new Container<E>(dlist.get(d));
  } else {
    final int c = search(clist, name);
    // When c >= 0, the element in current is a newly created element.
    return c < 0? null: new Container<E>(null);
  }
}
```

Key points of `DirectoryDiff::getChild` are as follows:

+ `INodesInPath::resolve` only cares about the `Diff` of the parent directory; any other `Diff` (such as the `Diff` of the parent's siblings) is ignored. This demonstrates Step 2, where irrelevant undo logs are filtered out by leveraging the directory tree structure.
+ `DirectoryDiff::getChild` searches the `Diff` instead of applying undo logs:
  + `DirectoryDiff::getChild` begins by searching the `Diff` corresponding to the snapshot specified by the user (e.g., s5 in /a/.snapshot/s5/b/c/d).
    + If the inode is found only in the deleted list of the `Diff` for snapshot s5, then it is visible to snapshot s5, as the visibility range is $(S_{created}, S_{deleted}]$.
    + If the inode is found only in the created list of the `Diff` for snapshot s5, then it is not visible to that snapshot.
    + If the inode appears in both the deleted and created lists of the `Diff` for snapshot s5, this indicates that the inode was first deleted and then recreated. In this case, the deleted inode is visible to snapshot s5.
    + If the inode is found in neither list, the method continues searching the posterior `Diff`.
  + If the inode cannot be found in the `Diff` for snapshot s5, the method proceeds to search in **posterior `Diff`s** (e.g., s6, s7, etc.), following the same logic.
  + If the search through posterior snapshots is exhausted, it means the inode does not appear in any undo logs from snapshot s5 to the current directory tree. In this case, it should simply be resolved in the current directory tree.
+ `Diff::accessPrevious` searches the deleted list first, then the created list, because of the scenario where an inode is deleted and then recreated within the same snapshot. As discussed in Step 3, "if an inode is deleted and then recreated, it will appear in both the deleted and created lists." Searching the deleted list first ensures that the inode is correctly treated as visible.

#### The Role of `INodeReference`: Viewing Rename as a Combination of Deletion and Creation

Ideally, Step 1 suggests treating a rename operation as a combination of a deletion followed by a creation. However, each inode manages certain resources (e.g., sub-inodes for a directory inode, blocks for a file inode), and storing a renamed inode as two separate inodes can complicate resource deallocation. To address this, HDFS introduces the concept of `INodeReference`. The following introduction is adapted from [here](https://hadoop.apache.org/docs/r3.4.1/hadoop-project-dist/hadoop-hdfs/build/source/hadoop-hdfs-project/hadoop-hdfs/target/api/org/apache/hadoop/hdfs/server/namenode/INodeReference.html):

> This class and its subclasses are used to support multiple access paths. A file/directory may have multiple access paths when it is stored in some snapshots, and it is renamed/moved to other locations.
>
> For example, (1) Suppose we have /abc/foo and the inode is inode(id=1000,name=foo). Suppose foo is created after snapshot s0, i.e. foo is not in s0 and inode(id=1000,name=foo) is in the create-list of /abc for the s0 diff entry. (2) Create snapshot s1, s2 for /abc, i.e. foo is in s1 and s2. Suppose sDst is the last snapshot /xyz. (3) mv /abc/foo /xyz/bar, i.e. inode(id=1000,name=...) is renamed from "foo" to "bar" and its parent becomes /xyz.
>
> Then, /xyz/bar, /abc/.snapshot/s1/foo and /abc/.snapshot/s2/foo are different access paths to the same inode, inode(id=1000,name=bar). Inside the inode tree, /abc/.snapshot/s1/foo and /abc/.snapshot/s2/foo indeed have the same resolved path, but /xyz/bar has a different resolved path.
>
> With references, we have the following - The source /abc/foo inode(id=1000,name=foo) is replaced with a WithName(name=foo,lastSnapshot=s2) and then it is moved to the delete-list of /abc for the s2 diff entry. The replacement also replaces inode(id=1000,name=foo) in the create-list of /abc for the s0 diff entry with the WithName. The same as before, /abc/foo is in s1 and s2, but not in s0. - The destination /xyz adds a child DstReference(dstSnapshot=sDst). DstReference is added to the create-list of /xyz for the sDst diff entry. /xyz/bar is not in sDst. - **Both WithName and DstReference point to another reference WithCount(count=2).** - Finally, WithCount(count=2) points to inode(id=1000,name=bar). Note that the inode name is changed to "bar".

However, the idea of viewing a rename operation as a combination of a deletion and a creation could be illustrated in the following aspects:

+ In the example above, the reference left in the src path's snapshots' `Diff`s is WithName(name=foo,lastSnapshot=s2), while the reference left in the dst path's snapshot's `Diff` is DstReference(dstSnapshot=sDst). Although both references point to the same inode, there is a conceptual splitting between them.
+ When determining the latest snapshot ID of the dst path, HDFS must filter out the snapshot IDs inherited from the src path before the rename. Specifically, the snapshot IDs associated with WithName(name=foo,lastSnapshot=s2) (from the src path) should be treated as part of the deleted inode and not as part of the newly created inode. The relevant part of the code in [`INodesInPath::resolve`](https://github.com/apache/hadoop/blob/96572764921706b1fecaf064490457d36d73ea6e/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/INodesInPath.java#L155-L162) is shown below:

```java
if (!isRef && isDir && dir.isWithSnapshot()) {
  // if the path is a non-snapshot path, update the latest snapshot.
  if (!isSnapshot && shouldUpdateLatestId(
      dir.getDirectoryWithSnapshotFeature().getLastSnapshotId(),
      snapshotId)) {
    snapshotId = dir.getDirectoryWithSnapshotFeature().getLastSnapshotId();
  }
}
```
