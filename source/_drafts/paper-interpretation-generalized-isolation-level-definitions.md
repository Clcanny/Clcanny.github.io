---
layout: post
title: Paper Interpretation - Generalized Isolation Level Definitions
date: 2023-01-17 00:20:53
categories:
  - [Computer Science, Serializability]
math: true
---

### Predicate-based Reads

$\mathbf{r}_i(\mathrm{P}: \operatorname{Vset}(\mathrm{P})) \mathrm{r}_i\left(\mathrm{x}_j\right) \mathrm{r}_i\left(\mathrm{y}_k\right) \ldots$

file:///Users/demons/Downloads/Philip%20A.%20Bernstein,%20Vassos%20Hadzilacos,%20Nathan%20Goodman%20-%20Concurrency%20Control%20and%20Recovery%20in%20Database%20Systems%20(1987,%20Addison%20Wesley%20Publishing%20Company)%20-%20libgen.li.pdf
View Serializability
is (conflict) equivalent to some serial history.
We can use the defini-
tion of view equivalence in a similar manner to arrive at a new concept of
serializability. Specifically, we define a history H to be view serializable

本篇文章的一个贡献是在多版本系统上定义了 conflicit ，从而定义了多版本系统的 conflicit serializaility.
需要解释的是：为什么 conflicit serializability 比 view serializability 更乐观，允许更多的 history ？
也许因为 conflicit 捕捉了冲突，然而不是所有 not view equivalent 都是冲突的？能不能举一个例子？
在 a critique to ansi sql 和 control and reocvery in database systems 里，我们无法定义多版本系统中的冲突，导致我们只能使用 view equivalent 这种比 conflicit equivalent 更加严格的等价关系，来把多版本系统的依赖关系转换成单版本系统的依赖关系。

Note that a predicate-based modification can also be modeled as a predicate-based read followed
by a set of writes on the matched objects.
将 predicated-based write 放松成 predicated-based read 具体会对 serializability 造成什么影响？
his technique provides weaker guarantees
(than the approach given above) to predicate-based modifications at lower isolation levels.
具体来说，lower 表示什么？
It is possible to change our definitions to allow such
semantics; we have chosen a different approach since we wanted to provide stronger guarantees for
predicate-based modifications at lower isolation levels.

If a query is used for generating the values, our model treats such an insert operation as a predicate-based read followed by a sequence of write events that correspond to the tuples being added.
如果将选取 values 这个过程模拟成 predicated-based write ，会导致什么结果？一个更加紧但是没必要这么紧的模型？如何证明这一点？
since the predicate is used to determine what tuples will be inserted in the Bonus relation
and not for determining which matched objects need to modified.
Modeling an insert operation as
a predicate-based read followed by a set of write events allows flexibility and ensures that some
commercial systems are not ruled out.
更多地还是照顾到了商业数据库？方便大家理解？

relations=table?
object=row?
A read operation based on predicate P only observes object versions in relations that are
specified by P (similarly for writes). We chose this approach rather than having a predicate-based
read observe versions of all objects in the database because an object x in a relation that is not
specified by P does not matter. The only way that x can match P is if its relation is changed to be
one of P’s relations. Since objects do not change relations in our model, we can ignore object x for
an operation based on predicate P since x’s relation is not specified by P. Alternatively, we could
say that the system chooses unborn versions of all objects in such relations.
对于在同一张表内但是不能被条件 P 选中的 rows ，因为要在被条件 P 筛选之前决定要哪些版本参与筛选，所以我们是知道它们的参选版本的，基于这个参选版本，我们才知道哪些 row 被选上了，哪些 row 没有被选上。所以不能说没被选上的 row 就不知道它的版本，不知道版本就不知道它会不会被选上，这是悖论。
不在同一张表上的 objects 是肯定不会被条件 P 选上的，所以我们可以不知道它们的版本。

两篇文章对 Directly predicate-read-depends 的定义不一样，我认为要简短的那篇文章更加合理。
有两个区别：从集合中删除 objects 的事务也算是依赖，不改变集合状态只是改变 objects（改变前后都在或者都不在集合内）的事务不算依赖。但长文章也对删除 objects 打了补丁：
if
Tj observes a dead version of some object, it directly read-depends on the transaction that
deleted that object.
那么其实只剩一个区别了：短文章认为只有改变集合状态才算是依赖，长文章认为选了这个版本就算是依赖。
The rule for predicate-read-dependencies captures the
idea that what matters for a predicate is the set of tuples that
match or do not match and not their values. Furthermore, of
all the transactions that have caused the tuples to match (or
not match) for rj (P: Vset(P)), we use the latest transaction
where a change to Vset(P) occurs rather than using the latest
transaction that installed the versions in Vset(P). This rule
ensures that we capture the minimum possible conflicts for
predicate-based reads.
`e.g. SELECT COUNT(*) WHERE P`?

// 短论文
Read-dependencies and anti-dependencies are treated
similarly for predicates, i.e., we add an edge whenever a
predicate’s matched set is changed. The difference between
item-anti-depends and predicate-anti-depends is also simi-
lar. For item-anti-depends, the overwriting transaction must
produce the very next version of the read object, while for
predicate-anti-depends it simply produces a later version
that changes the matched tuples of the predicate.
// 长论文
Note that read-dependencies are treated differently from anti-dependencies for predicates.
A
transaction Tj directly predicate-read-depends on all transactions that produced the versions in
Vset(P) However, if transaction Ti performs an operation ri (P: Vset(P)), Tj predicate-anti-depends
on Ti only if Tj ’s modifications change the set of objects that matched P; simply overwriting a
version in Vset(P) does not cause a predicate-anti-dependency. We avoid extra anti-dependency
edges originating from Ti since they can unnecessarily disallow legal histories.
// 短论文把 read-dependencies for predicateds 取消了，把 write-dependencies for predicates 叫做 read-dependenvies for predicates ，所以实际上使用 write-dependencies 取代了所有 read-dependencies ，是一种加强。
但它们等价吗？以及为什么要这么改？谁先谁后呢？

We say that Tj directly predicate-write-depends on Ti if either
1. Tj overwrites an operation wi (P: Vset(P)), or
  // overwrite = changes the matches
2. Tj executes an operation wj (Q: Vset(Q)) and xi 2 Vset(Q).
  // Ti 写入的版本被 Tj 以 predicate write 的形式使用了
  // 为什么要加入这个条件？
  // 短论文的 Directly predicate-read-depends 也包括了这个条件，只不过以更加简短的形式表达出来了。
ghost writes / ghost reads

Part (2) of predicate-write-depends is similar to predicate-anti-depends: in both cases, a trans-
action overwrites a predicate-based read or write of another transaction. As in the case of anti-
dependencies, we do not consider a transaction Tj to predicate-write-depend on Ti if Tj simply
overwrites a version in Vset(P) (of an operation wi (P: Vset(P))); instead Tj must change the objects
matched by P. Predicate-write-dependencies are chosen in this manner to prevent legal histories
from being unnecessarily disallowed.

Suppose that transaction Ti deletes a record x
that matches a predicate “social security number = SN” and a later transaction Tj inserts a record y
with the same social security number in the database. In our model, these two objects are distinct: Ti
creates the dead version of x and Tj creates the first visible version of y. Tj predicate-write-depends
on Ti since it changes the objects matched by Ti ’s predicate and installs a later version of y (Ti ’s
object set contains version yinit that does not match whereas yj matches the predicate).

可序列化的条件是值的写入顺序和 DSG 的依赖顺序不冲突？
注意值的写入顺序和事务条件顺序、write actions 的先后顺序都没有关系。

Anti-depends: We say that a transaction Tj anti-depends on Ti if it conflict-depends on Ti but does
not depend on Ti , i.e., the path from Ti to Tj contains at least one anti-dependency edge.
// Anti-depends 不要求全部路径是由 directly anti-depends 构成的。

G = general
enough to allow locking and optimistic implementations
PL = portable level

为什么 P0 不是一个好的描述？
However, recall that P0 rules out efficient optimistic
and multi-version mechanisms by disallowing concurrent writes that conflict. Thus, to allow a range
of concurrency control mechanisms, assumptions about a particular recovery implementation must
not be made in the consistency specifications and different recovery mechanisms must be permitted.

G0: Write Cycles. A history H exhibits phenomenon G0 if DSG(H) contains a directed
cycle consisting entirely of write-dependency edges.
为什么要禁止 G0 ？值的写入顺序不是由系统决定的吗？系统完全可以把存在写冲突的两个值的四个版本，控制成可序列化的四个版本？可不可能存在一种 history ，违反 G0 但是可序列化？
H?: x0x1y1y0c1c2, x0 << x1, y0 << y1
注意：虽然 y1 先于 y0 ，但是系统决定版本y0 先于版本 y1 。这个例子是盲写的例子，所以违反了 G0 也无所谓？anyway 好像不太合理的样子？所以后面关于 completeness 的证明有问题？

1-serial MV history 才可以等价于 serial SV history ，1-serial MV history 要求事务必须读最新版本的值，本篇论文在论证 serializability 的 correctness 时有用到这个条件吗？

G1a: Aborted Reads.
G1b: Intermediate Reads.
G1c: Circular Information Flow.

Note that G1c includes G0.
We could have defined a weaker version of G1c that only concerned cycles having at least one
read-dependency edge, but it seems simpler not to do this.
这堵上了我们之前盲写的例子：H?: x0x1y1y0c1c2, x0 << x1, y0 << y1

// 为什么比 Pn 弱？
Proscribing G1 is clearly weaker than proscribing P1 since G1 allows transactions to read
from uncommitted transactions. The lock-based implementation of PL-2 disallows G1 because the
combination of long write-locks and short read-locks ensures that if Ti reads a version produced by
Tj , Tj must have committed already and therefore it cannot read a version produced by T i .

The PL-2 definition given in this section treats predicate-based reads like normal reads and provides
no extra guarantees for them.
// Why?
什么是 extra guarantees ？换句话说，只承诺了集合内的每个 items 不能违反 G1a 和 G1b ，没有说整个集合要满足什么样的性质。e.g. 所有 object versions 来自同一个 snapshot 。
Each predicate-based read:
1. provided the same guarantees as a normal read.
2. indivisible with respect to any predicate-based write. // G1 只要求 predicate-base write 和 predicate-base read 不能成环，对单个 predicated-base read 读到什么样的数据是没有做规范的。
3. indivisible with respect to all writes of a transaction. // 同理，只要不成环就行，没有要求要读到什么样的数据。

w1 (Dept=Sales: x0 ; y0 ) w1 (x1 ) w1 (y1 )
类似上面的写法是不是在说，我们应该认为 predicated write 之后的所有 w/r? 都从属与这次 predicated write ？
因为哪怕 y0 没有被选中，transaction 也仍然有可能利用了“y0 没有被选中”来决定 y1 （下一次写入）的值？
w1(P1:...)...w1(P2:...)...w1(x1) 是不是应该认为 w1(x1) 同时归属于 w1(P1:...) 和 w1(P2:...) ？

// 为什么是 wj (xj ) ？什么叫做 due to ？
// 应该是写错了，是 wi(xi)
G1-predA: Non-atomic Predicate-based Reads. A history H exhibits phenomenon
G1-predA if H contains distinct committed transactions Ti and Tj , and operations
wi (P: Vset(P)), wi (xi ) : : : wi (yi ) and rj (Q: Vset(Q)) such that wi (xi ) and wj (xj )
are events generated due to wi (P: Vset(P)), xi 2 Vset(Q), and wi (yi ) overwrites
rj (Q: Vset(Q)).
xi 选中了，但是没有选中 yi ，且 y 的版本要么选中了 just 之前的版本，要么选中了 just 之后的版本，且恰好不同时满足条件 Q 。overwrite = change match with?
这要求我们：如果有一个 yi ，恰好改变了 y(just-before-i) 或者 y(just-before-j) 满足条件 Q 的关系，那么其它 objects 的 versions 必须来自同一个事务（如果该事务也写了这些 objects 的话）。
但如果没有改变条件 Q ，那么可以随便选，不违反 G1-predA ，why ？
H-alloied-by-G1-predA: w1(P:x0;y0)w1(x1)w1(y1)c1w2(P:x1;y1)w2(x2)w2(y2)c2w3(P:x2;y2)w3(x3)w3(y3)c3w4(P:x3;y3)w4(x4)w4(y4)c4r5(Q:x2;y3)r5(x2)c5
假设 P(x1) = P(x2) = P(x3) = P(x4) = true, P(y1) = P(y2) = P(y3) = P(y4) = true, 那么 H-alloied-by-G1-predA 是合法的。
// overwrite != change match with, 之前的理解是错的
Disallowing G1-predA guarantees that if Ti ’s predicate-based read observes an update by Tj ’s
predicate-based write, it does not see any version older than the ones installed by Tj ’s write.

G1-predB: Non-atomic Predicate-based Reads with respect to Transactions.???
到底应该怎么理解 overwrite ？

// view-serializability 和 conflict-serializability 的关系是什么？
// https://www.geeksforgeeks.org/difference-between-conflict-and-view-serializability/
If a schedule is view serializable then it may or may not be conflict serializable.
If a schedule is conflict serializable then it is also view serializable schedule.
conflict-serializability 比 view-serializability 更窄。
// https://stackoverflow.com/questions/32941901/view-serializable-and-conflict-serializable
Now because conflict serializable is more stringent than view serializable.
Blind writes appear in any schedule that is view serializable but not conflict seralizable.
// https://gateoverflow.in/106187/test-by-bikram-mock-gate-test-1-question-25
Any view serializable schedule that is not conflict serializable must contain a blind write.
But presence of blind write doesnt mean that a given view serializable schedule is not conflict serializable. i.e., there are view serializable schedules with blind writes that are
1. conflict serializable
2. non conflict-serializable
// https://stackoverflow.com/questions/20529800/whats-the-difference-between-conflict-serializable-and-serializable
Every conflict serializable schedule is serializable.
// https://gateoverflow.in/292262/self-doubt-blind-write
// https://cs.stackexchange.com/questions/145031/understanding-the-behavior-of-conflict-serializability-and-view-serializability
// https://xuanhien.files.wordpress.com/2011/04/database-management-systems-raghu-ramakrishnan.pdf
Every conflict serializable schedule is view serializable, although the converse is not true.
This is not a coincidence; it can be shown that any view serializable schedule that is not conflict serializable contains a blind write.
Figure 19.10 Venn Diagram for Classes of Schedules

However, instead of preventing those conflicts from
occurring at transaction execution time, our definitions place constraints on the transactions that
are allowed to commit.

We can prove the equivalence of our PL-3 conditions with conflict-serializability using the proof
given in [GR93]; our DSGs are similar to their graphs. This equivalence can also be proved along
the lines of the proof given in [BHG87] for view-serializability.
// 细节？
我们不关注更低级别的隔离性的正确性和完备性的证明。
Flexibility Theorem

Consistency Guarantees for Executing Transactions
// 分布式文件系统的元数据系统也需要 ececuting transactions 的隔离性，方便验证逻辑是否符合预期。
Debugging also becomes more difficult for an application programmer; if the transaction observes a broken invariant, it may be difficult for the programmer to determine whether the invariant was violated due to a code bug or due to weak consistency guarantees provided to executing transactions by the system.
Thus, if strong guarantees are not provided to executing transactions, a programmer must take temporary inconsistencies into account in the application code.
在碰到元数据不一致的时候，我们会直接 coredump ，但是如果背后是一个不承诺执行中事务隔离性的数据库，直接 coredump 就不是一个合理的行为，abort 当前事务才是合理的操作。但是我们就不会知道这种不一致究竟是因为我们的代码写得有问题导致的，还是 db 提供的隔离性不够导致的。但是 hdfs 的元数据系统本身并不需要对外承诺 executing transaction 的一致性，所以这一章可以忽略。或者简单地了解一下理论，不做过多探讨。
Since a transaction can determine whether it is executing below a certain degree only by observing the state of the database, our conditions will provide guarantees only for reads of uncommitted transactions and not for their writes. 换言之，只需要提供读冲突检测即可，写冲突检测在推迟到提交的时候再检测。
For the purpose of providing consistency guarantees to an executing transaction Ti , we consider
Ti ’s predicate-based writes as predicate-based reads. 为什么？

A partial order to relate various isolation levels.

To provide serializability for committed transactions in these systems, we use an optimistic
scheme called C LOCC [Ady94, AGLM95, Gru97]. This scheme has been shown to outperform the
best-known locking implementation, ACBL [CFZ94, ZCF97], in a client-server system [Gru97]
on many workloads.

CLOCC has been designed to work well for environments where all operations are
executed by clients.
hdfs namenode on kv store 就是一个典型的 client ，namenode 可以 cache kv store 的数据。
1. In environments where servers may perform part of the work, another scheme
called AACC (Asynchronous Avoidance-based Cache Consistency) has been shown to outperform
CLOCC [OVU98].
2. Both CLOCC and ACBL are not expected to perform well in workloads where
there are hotspots, i.e., high contention on a single or very few objects. For such cases, mechanisms
such as field calls [Reu82] and escrow reads [O’N86] are known to offer superior performance.
CLOCC 回答了多个 namenode 如何维护 kv 缓存的问题？

标准的两阶段提交：由 coordinator 原子性地决定事务是否生效
Phase 1
includes two log updates to stable storage, but the optimizations suggested by Stamos [Sta89] can
reduce this to a single log update.

The
server maintains an invalid set for each client D and adds the list of obsolete objects (because of Ti ’s
modifications) to D’s invalid set. It informs clients about these old objects by sending invalidation
messages to them.
// 这可以通过 client server 间的 heartbeat 来做
但是我们很难依赖 kv 提供这样的机制
对于一个特定的 key ，本质上只有一个 namenode 会负责，所以也不需要 invalidate 机制
我们有没有可能打破上面那个假设，把 namenode 做到 client 里去？或者说，取消 partition 概念，每个 namenode 都是平等的，代替 client 提交 transaction ？用 Raft + RocksDB 做 KV Server 就可以自带 invlaidate 机制。
To avoid refetching these modified objects after an
abort, the client maintains an undo log; before any object is updated, the client makes a copy of the
object. Thus, when the transaction aborts, the updated objects are simply reverted to their original
state unless they have been invalidated; this simple optimization is very important in enhancing
C LOCC’s performance.
CLOCC 甚至在客户端准备了 undo log 来避免频繁刷新缓存。

a cached set for client C contains the identifiers of the
pages containing objects cached at C rather than individual object identifiers.
是分 slice 的思路

// ChatGPT
Backward validation and forward validation are two approaches to ensuring transaction consistency in database systems.
Backward Validation: In backward validation, transactions are validated in reverse order from the order in which they committed. That is, the most recent transaction is validated first, then the next most recent transaction, and so on. The idea behind this approach is that if the most recent transaction is consistent with the database state, then all previous transactions must also be consistent with the database state. If a transaction is found to be inconsistent with the database state, then it and all subsequent transactions are rolled back.
Forward Validation: In forward validation, transactions are validated in the order in which they committed. Each transaction is checked for consistency with the database state at the time it was committed. If a transaction is found to be inconsistent with the database state, then it is rolled back and all subsequent transactions are also rolled back.

We define the following
relationship for conflicts: two transactions conflict if one has modified an object that the other has

To simplify our algorithm, we arrange the read set to always contain the write set.
这种简化是怎么发生的？不这么假设的话，到底会有多复杂？
read or modified.
