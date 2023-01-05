---
layout: post
title: Paper Interpretation - A Critique of ANSI SQL Isolation Levels
date: 2023-01-05 23:56:24
categories:
  - [Computer Science, Serializability]
---

This article reorganizes the structure of the original paper to make it easier to understand (at least in my opinion), quotes some important content from its reference, and adds my personal understanding of some confusing details (although it may be wrong).

# Terminology

+ A **transaction** groups a set of actions that transform the database from one consistent state to another.
+ A **history** models the interleaved execution of a set of transactions as a linear ordering of their actions, such as Reads and Writes (i.e., inserts, updates, and deletes) of specific data items.
+ The actions of committed transactions in the history are represented as graph nodes. If action `op1` of transaction `T1` conflicts with and precedes action `op2` of transaction `T2` in the history, then the pair `<op1, op2>` becomes an edge in the **dependency graph**.
+ Two histories are equivalent if they have the same committed transactions and the same dependency graph.
+ **Phenomena** are the much broader interpretations of **anomalies**. **Anomalies** are strict interpretations of **phenomena**.
  + Let's take dirty read as an example. ANSI SQL Isolation defines dirty read as follows: Transaction `T1` modifies a data item. Another transaction `T2` then reads the data item before `T1` executes a COMMIT or ROLLBACK. If `T1` then performs a ROLLBACK, `T2` has read a data item that was never committed and so never really existed.
  + The board interpretation is `P1: w1[x]...r2[x]...((c1 or a1) and (c2 or a2) in any order)`, and `P` is the capital first character of the word phenomena.
  + The strict interpretation is `A1: w1[x]...r2[x]...(a1 and c2 in any order)`, and `A` is the capital first character of the word anomaly.
  + `P1` is a much broader interpretation than `A1`, since it prohibits all four possible commit-abort pairs by transactions `T1` and `T2`, while `A1` only prohibits two of the four.
+ **Predicate lock** is used to resolve conflicting actions that occur on a set of data items.

# Isolation Levels Defined By GLPT & Locking Isolation Levels

## Isolation Levels Defined By GLPT

[Granularity of Locks and Degrees of Consistency in a Shared Data Base, by J.N. Gray, R.A. Lorie, G.R. Putzolu and I.L. Traiger](https://web.stanford.edu/class/cs245/readings/granularity-of-locks.pdf) defined Degrees of Consistency in three ways: locking, data-flow graphs, and anomalies. The anomaly definitions were too vague. The authors continue to get criticism for that aspect of the definitions in [Transaction Processing: Concepts and Technique, by Jim Gray and Andreas Reuter](https://dl.acm.org/doi/10.5555/573304). Only the more mathematical definitions in terms of histories and dependency graphs or locking have stood the test of time.

> + Definition 1 (anomalies):
>   + Degree 3: Transaction `T` sees degree 3 consistency if:
>     + `T` does not overwrite dirty data of other transactions.
>     + `T` does not commit any writes until it completes all its writes (i.e. until the end of transaction).
>     + `T` does not read dirty data from other transactions.
>     + Other transactions do not dirty any data read by `T` before `T` completes.
>   + Degree 2: Transaction `T` sees degree 2 consistency if:
>     + `T` does not overwrite dirty data of other transactions.
>     + `T` does not commit any writes before EOT.
>     + `T` does not read dirty data of other transactions.
>   + Degree 1: Transaction `T` sees degree 1 consistency if:
>     + `T` does not overwrite dirty data of other transactions.
>     + `T` does not commit any writes before EOT.
>   + Degree 0: Transaction `T` sees degree 0 consistency if:
>     + `T` does not overwrite dirty data of other transactions.
> + Definition 2 (locking):
>   + Degree 3: Transaction `T` observes degree 3 lock protocol if:
>     + `T` sets a long exclusive lock on any data it dirties.
>     + `T` sets a long share lock on any data it reads.
>   + Degree 2: Transaction `T` observes degree 2 lock protocol if:
>     + `T` sets a long exclusive lock on any data it dirties.
>     + `T` sets a (possibly short) share lock on any data it reads.
>   + Degree 1: Transaction `T` observes degree 1 lock protocol if:
>     + `T` sets a long exclusive lock on any data it dirties.
>   + Degree 0: Transaction `T` observes degree 0 lock protocol if:
>     + `T` sets a (possibly short) exclusive lock on any data it dirties.
> + Definition 2' (locking):
>   + Degree 3: `T` is well formed and `T` is two phase.
>   + Degree 2: `T` is well formed and `T` is two phase with respect to writes.
>   + Degree 1: `T` is well formed with respect to writes and `T` is two phase with respect to writes.
>   + Degree 0: `T` is well formed with respect to writes.
> + Definition 3 (data-flow graphs):
>   + Suppose that transaction `T` performs action `a` on entity `e` at some step in the schedule and that transaction `T'` performs action `a'` on entity `e` at a later step in the schedule. Further suppose that `T` does not equal `T'`. Then:
>     + `T <<< T'`
>       + if `a` is a write action and `a'` is a write action
>       + or `a` is a write action and `a'` is a read action
>       + or `a` is a read action and `a'` is a write action
>     + `T << T'`
>       + if `a` is a write action and `a'` is a write action
>       + or `a` is a write action and `a'` is a read action
>     + `T < T'`
>       + if `a` is a write action and `a'` is a write action
>   + Let `<*` be the transitive closure of `<`.
>   + A schedule is degree 1 (2 or 3) consistent if and only if the relation `<*` (`<<*` or `<<<*`) is a partial order.

## Locking Isolation Levels

The ANSI isolation levels are related to the behavior of lock schedulers.

## Table 2: Degrees of Consistency and Locking Isolation Levels defined in terms of locks

Consequently, it is necessary to differentiate isolation levels defined in terms of locks from the ANSI SQL phenomenabased isolation levels. To make this distinction, the levels in Table 2 are labeled with the "Locking" prefix, as opposed to the "ANSI" prefix of Table 1.

| Consistency Level = Locking Isolation Level | Read Locks on Data Items and Predicates (the same unless noted)                                    | Write Locks on Data Items and Predicates (always the same) |
| :------------------------------------------ | :------------------------------------------------------------------------------------------------- | :--------------------------------------------------------- |
| Degree 0                                    | none required                                                                                      | Well-formed Writes                                         |
| Degree 1 = Locking READ UNCOMMITTED         | none required                                                                                      | Well-formed Writes<br/>Long duration Write locks           |
| Degree 2 = Locking READ COMMITTED           | Well-formed Reads<br/>Short duration Read locks (both)                                             | Well-formed Writes<br/>Long duration Write locks           |
| Cursor Stability                            | Well-formed Reads<br/>Read locks held on current of cursor<br/>Short duration Read Predicate locks | Well-formed Writes<br/>Long duration Write locks           |
| Locking REPEATABLE READ                     | Well-formed Reads<br/>Long duration data-item Read locks<br/>Short duration Read Predicate locks   | Well-formed Writes<br/>Long duration Write locks           |
| Degree 3 = Locking SERIALIZABLE             | Well-formed Reads<br/>Long duration Read locks (both)                                              | Well-formed Writes<br/>Long duration Write locks           |

The fundamental serialization theorem is that well-formed two-phase locking guarantees serializability — each history arising under two-phase locking is equivalent to some serial history. Conversely, if a transaction is not well-formed or two-phased then, except in degenerate cases, non-serializable execution histories are possible [EGLT].

We say Locking SERIALIZABLE == Serializable even though it is well known that a locking scheduler does not admit all possible Serializable histories.

# ANSI SQL Isolation Levels

## Phenomena & Anomaly

+ Dirty Read: Transaction `T1` modifies a data item. Another transaction `T2` then reads that data item before `T1` performs a COMMIT or ROLLBACK. If `T1` then performs a ROLLBACK, `T2` has read a data item that was never committed and so never really existed.
+ Non-repeatable or Fuzzy Read: Transaction `T1` reads a data item. Another transaction `T2` then modifies or deletes that data item and commits. If `T1` then attempts to reread the data item, it receives a modified value or discovers that the data item has been deleted.
+ Phantom: Transaction `T1` reads a set of data items satisfying some `<search condition>`. Transaction `T2` then creates data items that satisfy `T1`'s <search condition> and commits. If `T1` then repeats its read with the same `<search condition>`, it gets a set of data items different from the first read.

| Phenomena                    | Histories                                                        |
| ---------------------------- | ---------------------------------------------------------------- |
| Dirty Read                   | `P1: w1[x]...r2[x]...((c1 or a1) and (c2 or a2) in any order)`   |
|                              | `A1: w1[x]...r2[x]...(a1 and c2 in any order)`                   |
| Non-repeatable or Fuzzy Read | `P2: r1[x]...w2[x]...((c1 or a1) and (c2 or a2) in any order)`   |
|                              | `A2: r1[x]...w2[x]...c2...r1[x]...c1`                            |
| Phantom                      | `P3: r1[P]...w2[y in P]...((c1 or a1) and (c2 or a2) any order)` |
|                              | `A3: r1[P]...w2[y in P]...c2...r1[P]...c1`                       |

## Table 1: ANSI SQL Isolation Levels Defined in terms of the Three Original Phenomena

| Isolation Level       | `P1` (or `A1`)<br/>Dirty Read | `P2` (or `A2`)<br/>Fuzzy Read | `P3` (or `A3`)<br/>Phantom |
| --------------------- | ----------------------------- | ----------------------------- | -------------------------- |
| ANSI READ UNCOMMITTED | Possible                      | Possible                      | Possible                   |
| ANSI READ COMMITTED   | Not Possible                  | Possible                      | Possible                   |
| ANSI REPEATABLE READ  | Not Possible                  | Not Possible                  | Possible                   |
| ANOMALY SERIALIZABLE  | Not Possible                  | Not Possible                  | Not Possible               |

Disallowing the three phenomena does not imply serializability, so Table 1 calls it ANOMALY SERIALIZABLE.

# Enhanced ANSI SQL Isolation Levels

## Remark 3: ANSI SQL isolation should be modified to require `P0` for all isolation levels.

Dirty Write: Transaction `T1` modifies a data item. Another transaction `T2` then further modifies that data item before `T1` performs a COMMIT or ROLLBACK. If `T1` or `T2` then performs a ROLLBACK, it is unclear what the correct data value should be. The broad interpretation of this is:

`P0: w1[x]...w2[x]...((c1 or a1) and (c2 or a2) in any order)`

Why Dirty Writes are bad?

+ They can violate database consistency. Assume there is a constraint between `x` and `y` (e.g., `x=y`), and `T1` and `T2` each maintain the consistency of the constraint if run alone. However, the constraint can easily be violated if the two transactions write `x` and `y` in different orders, which can only happen if there are Dirty writes. For example consider the history `w1[x]w2[x]w2[y]c2w1[y]c1`. `T1`'s changes to `y` and `T2`'s to `x` both "survive". If `T1` writes 1 in both `x` and `y` while `T2` writes 2, the result will be `x=2`, `y=1` violating `x=y`.
+ Without protection from `P0`, the system can't undo updates by restoring before images. Consider the history: `w1[x]w2[x]a1`. You don't want to undo `w1[x]` by restoring its before-image of `x`, because that would wipe out `w2`'s update. But if you don't restore its before-image, and transaction `T2` later aborts, you can't undo `w2[x]` by restoring its before-image either! (We assume that each operation remembers at most one before-image of a variable (e.g. `x`) written by another transaction.)

So even the weakest locking systems hold long duration write locks. Otherwise, their recovery systems would fail. Then we get remark 3.

Remark 3: ANSI SQL isolation should be modified to require `P0` for all isolation levels.

## Remark 4: ANSI meant to define `P1`, `P2`, and `P3` instead of `A1`, `A2`, and `A3`.

Remark 4. Strict interpretations `A1`, `A2`, and `A3` have unintended weaknesses. The correct interpretations are the Broad ones. We assume in what follows that ANSI meant to define `P1`, `P2`, and `P3`.

+ `H1: r1[x=50]w1[x=10]r2[x=10]r2[y=50]c2r1[y=50]w1[y=90]c1`. `H1` is non-serializable, because transaction `T1` is transferring a quantity 40 from `x` to `y`, maintaining a total balance of 100, but `T2` reads an inconsistent state where the total balance is 60. H1 does not violate any of the anomalies `A1`, `A2`, or `A3`, but violates the broad interpretation of `A1`, the phenomenon `P1`.
+ `H2: r1[x=50]r2[x=50]w2[x=10]r2[y=50]w2[y=90]c2r1[y=90]c1`. `H2` is non-serializable, because transaction `T1` sees a total balance of 140. `H2` does not violate any of the anomalies `A1`, `A2`, or `A3`, but violates the broad interpretation of `A2`, the phenomenon `P2`.
+ `H3: r1[P]w2[insert y in P]r2[z]w2[z]c2r1[z]c1`. Here `T1` performs a `<search condition>` to find the list of active employees. Then `T2` performs an insert of a new active employee and then updates `z`, the count of employees in the company. Following this, `T1` reads the count of active employees as a check and sees a discrepancy. This history is clearly not serializable, but is allowed by `A3` since no predicate is evaluated twice. Again, the Broad interpretation solves the problem.

## Table 3: Enhanced ANSI SQL Isolation Levels Defined in terms of the four phenomena

| Isolation Level  | `P0`<br/>Dirty Write | `P1`<br/>Dirty Read | `P2`<br/>Fuzzy Read | `P3`<br/>Phantom |
| ---------------- | -------------------- | ------------------- | ------------------- | ---------------- |
| READ UNCOMMITTED | Not Possible         | Possible            | Possible            | Possible         |
| READ COMMITTED   | Not Possible         | Not Possible        | Possible            | Possible         |
| REPEATABLE READ  | Not Possible         | Not Possible        | Not Possible        | Possible         |
| SERIALIZABLE     | Not Possible         | Not Possible        | Not Possible        | Not Possible     |

# Difference Between Locking Isolation Levels And ANSI SQL Isolation Levels

Locking isolation levels are more isolated than the same-named ANSI levels. Locking READ UNCOMMITTED provides long duration write locking to avoid a phenomenon called "Dirty Writes," but ANSI SQL does not exclude this anomalous behavior other than ANSI SERIALIZABLE.

Remark 6. For single version histories, it turns out that the `P0`, `P1`, `P2`, `P3` phenomena are disguised versions of locking. Thus the **enhanced** ANSI SQL isolation levels of Table 3 defined by these phenomena provide the same behavior as the locking isolation levels of Table 2:

+ Prohibiting `P0` precludes a second transaction writing an item after the first transaction has written it, equivalent to saying that long-term Write locks are held on data items (and predicates).
+ Prohibiting `P1` is equivalent to having well-formed reads on data items.
+ Prohibiting `P2` means long-term Read locks on data items.
+ Prohibiting `P3` means long-term Read predicate locks.

And we infer that locking isolation levels are more isolated than the same-named ANSI levels in another way:

+ Locking READ UNCOMMITTED == (ENHANCED) READ UNCOMMITTED >> ANSI READ UNCOMMITTED
+ Locking READ COMMITTED == (ENHANCED) READ COMMITTED >> ANSI READ COMMITTED
+ ...

# Other Isolation Types

## Cursor Stability

### Lost Update

Lost Update: The lost update anomaly occurs when transaction `T1` reads a data item and then `T2` updates the data item (possibly based on a previous read), then `T1` (based on its earlier read value) updates the data item and commits. In terms of histories, this is:

`P4: r1[x]...w2[x]...w1[x]...c1`

The problem, as illustrated in history `H4`, is that even if `T2` commits, `T2`'s update will be lost.

`H4: r1[x=100]r2[x=100]w2[x=120]c2w1[x=130]c1`

### Cursor Stability

Cursor Stability is designed to prevent the lost update phenomenon.

This is an example of using MySQL Cursor from [MySQL Tutorial: MySQL Cursor](https://www.mysqltutorial.org/mysql-cursor/):

```sql
DECLARE curEmail CURSOR FOR SELECT email FROM employees;
OPEN curEmail;
getEmail: LOOP
  FETCH curEmail INTO emailAddress;
  IF finished = 1 THEN
    LEAVE getEmail;
  END IF;
  -- Build email list.
  SET emailList = CONCAT(emailAddress, ";", emailList);
END LOOP getEmail;
CLOSE curEmail;
```

The Cursor Stability isolation level extends READ COMMITTED locking behavior for SQL cursors by adding a new read action for FETCH from a cursor and requiring that a lock be held on the current item of the cursor.

+ The lock is held until the cursor moves or is closed, possibly by a commit.
+ Naturally, the Fetching transaction can update the row, and in that case a write lock will be held on the row until the transaction commits, even after the cursor moves on with a subsequent Fetch.
+ The notation is extended to include, `rc`, meaning read cursor, and `wc`, meaning write the current record of the cursor. A `rc1[x]` and a later `wc1[x]` precludes an intervening `w2[x]`.

`P4`, renamed `P4C`, is prevented in this case: `P4C: rc1[x]...w2[x]...w1[x]...c1`.

### Remark 7: Strength of Cursor Stability

Remark 7: READ COMMITTED << Cursor Stability << REPEATABLE READ

The technique of putting a cursor on an item to hold its value stable can be used for multiple items, at the cost of using multiple cursors. Thus the programmer can parlay Cursor Stability to effective Locking REPEATABLE READ isolation for any transaction accessing a small, fixed number of data items. However this method is inconvenient and not at all general. Thus there are always histories fitting the `P4: r1[x]...w2[x]...w1[x]...c1` (when the user does not access `x` carefully by Cursor and FETCH?) (and of course the more general `P2: r1[x]...w2[x]...((c1 or a1) and (c2 or a2) in any order)`) phenomenon that are not precluded by Cursor Stability.

### Table 4.1: Enhanced ANSI SQL Isolation Levels Defined in terms of the six phenomena

| Isolation Level                  | `P0`<br/>Dirty Write | `P1`<br/>Dirty Read | `P4C`<br/>Cursor Lost Update | `P4`<br/>Lost Update | `P2`<br/>Fuzzy Read | `P3`<br/>Phantom |
| ----------------------------     | -------------------- | ------------------- | ---------------------------- | -------------------- | ------------------- | ---------------- |
| READ UNCOMMITTED<br/>== Degree 1 | Not Possible         | Possible            | Possible                     | Possible             | Possible            | Possible         |
| READ COMMITTED<br/>== Degree 2   | Not Possible         | Not Possible        | Possible                     | Possible             | Possible            | Possible         |
| Cursor Stability                 | Not Possible         | Not Possible        | Not Possible                 | Sometimes Possible   | Sometimes Possible  | Possible         |
| REPEATABLE READ                  | Not Possible         | Not Possible        | Not Possible                 | Not Possible         | Not Possible        | Possible         |
| SERIALIZABLE<br/>== Degree 3     | Not Possible         | Not Possible        | Not Possible                 | Not Possible         | Not Possible        | Not Possible     |

Why use the term "**Sometimes Possible**" other than "**Possible**" to describe the relationship between `P4`/`P2` and Cursor Stability? My understanding is: Users can avoid Lost Update or Fuzzy Read by using Cursor and FETCH, but Lost Update or Fuzzy Read can still happen if users don't use Cursor and FETCH correctly.

## Snapshot Isolation

Each transaction reads data from a snapshot of the (committed) data as of the time the transaction started, called its Start-Timestamp. This time may be any time before the transaction’s first Read. The transaction's writes (updates, inserts, and deletes) will also be reflected in this snapshot, to be read again if the transaction accesses (i.e., reads or updates) the data a second time. Updates by other transactions active after the transaction Start-Timestamp are invisible to the transaction.

When the transaction `T1` is ready to commit, it gets a Commit-Timestamp, which is larger than any existing Start-Timestamp or Commit-Timestamp. The transaction successfully commits only if no other transaction `T2` with a Commit-Timestamp in `T1`'s execution interval \[Start-Timestamp, Commit-Timestamp\] wrote data that `T1` also wrote. Otherwise, `T1` will abort.

When `T1` commits, its changes become visible to all transactions whose Start-Timestamps are larger than `T1`'s Commit-Timestamp.

### How to analyze the strength of Snapshot Isolation: Map MV histories to SV histories

[Concurrency Control and Recovery in Database Systems, by Philip Bernstein, Vassos Hadzilacos and Nathan Goodman, Chapter 2.6: VIEW EQUIVALENCE](https://www.amazon.com/Concurrency-Control-Recovery-Database-Systems/dp/0201107155) tells us:

> We want to define equivalence so that two histories are equivalent if they have the same effects. The effects of a history are the values produced by the Write operations of unaborted transactions. Since we don't know anything about the computation that each transaction performs, we don't know much about the value written by each Write. All we do know is that it is some function of the values read by each of the transaction's Reads that preceded the Write. Thus, if each transaction's Reads read the same value in two histories, then its Writes will produce the same values in both histories. From this observation and a little careful thought, we can see that (1) if each transaction reads each of its data items from the same Writes in both histories, then all Writes write the same values in both histories, and (2) if for each data item `x`, the **final Write** on `x` is the same in both histories, then the final value of all data items will be the same in both histories. And if all Writes write the same values in both histories and leave the database in the same final state, then the histories must be equivalent.
>
> Two histories are view equivalent if they have the same reads-from relationships and the same final writes.

[Concurrency Control and Recovery in Database Systems, by Philip Bernstein, Vassos Hadzilacos and Nathan Goodman, Chapter 5: MULTIVERSION CONCURRENCY CONTROL, Analyzing Correctness](https://www.amazon.com/Concurrency-Control-Recovery-Database-Systems/dp/0201107155) also tells us:

> Only a subset of serial MV histories, called 1-serial MV histories, are equivalent to serial 1V histories.
>
> For example, `w0[x=x0]w0[y=y0]c0r1[x=x0]r1[y=y0]w1[x=x1]w1[y=y1]c1r2[x=x0]r2[y=y1]c2` is a serial MV history, but not equivalent to a serial 1V history.

But are all (serial/non-serial) MV histories equivalent to (non-serial) 1V histories? I think the answer is yes, but how to prove it?

In [An Investigation of Transactional Isolation Levels, by P. O'Neil, E. O'Neil, H. Berenson, P.Bernstein, J. Gray and J. Melton](), we show that all Snapshot Isolation histories can be mapped to single-valued histories while preserving dataflow dependencies (the MV histories are said to be View Equivalent with the SV histories). For example:

+ `H1: r1[x=50]w1[x=10]r2[x=10]r2[y=50]c2r1[y=50]w1[y=90]c1` is a non-serializable history. `T1` is transferring a quantity 40 from `x` to `y`, maintaining a total balance of 100, but `T2` reads an inconsistent state where the total balance is 60.
+ Under Snapshot Isolation, the same sequence of actions would lead to the multi-valued history: `H1.SI: r1[x0=50]w1[x1=10]r2[x0=50]r2[y0=50]c2r1[y0=50]w1[y1=90]c1`.
+ The MV history `H1.SI` would map to the serializable SV history: `H1.SI.SV: r1[x=50]r1[y=50]r2[x=50]r2[y=50]c2w1[x=10]w1[y=90]c1`.

Mapping of MV histories to SV histories is the only rigorous touchstone needed to place Snapshot Isolation in the Isolation Hierarchy.

### Snapshot Isolation is non-serializable

`H5: r1[x=50]r1[y=50]r2[x=50]r2[y=50]w1[y=-40]w2[x=-40]c1c2`

`H5` is non-serializable and has the same inter-transactional dataflows as could occur under Snapshot Isolation (there is no choice of versions read by the transactions). Here we assume that each transaction that writes a new value for `x` and `y` is expected to maintain the constraint that `x + y` should be positive, and while `T1` and `T2` both act properly in isolation, the constraint fails to hold in `H5`.

### Strength of Snapshot Isolation

#### Remark 8: READ COMMITTED << Snapshot Isolation

In Snapshot Isolation, first-committer-wins precludes `P0` (dirty writes), and the timestamp mechanism prevents `P1` (dirty reads), so Snapshot Isolation is no weaker than READ COMMITTED. In addition, `A5A` is possible under READ COMMITTED, but not under the Snapshot Isolation timestamp mechanism.

#### Remark 9: REPEATABLE READ >><< Snapshot Isolation

+ Write Skew (`A5B`) obviously can occur in a Snapshot Isolation history (e.g., `H5`), and in the Single Valued history interpretation we've been reasoning about, forbidding `P2` also precludes `A5B`. Therefore Snapshot Isolation admits history anomalies that REPEATABLE READ does not.
  + `A5` (Data Item Constraint Violation): Suppose `C()` is a database constraint between two data items `x` and `y` in the database. Here are two anomalies arising from constraint violation:
    + `A5A` (Read Skew). Suppose transaction `T1` reads `x`, and then a second transaction `T2` updates `x` and `y` to new values and commits. If now `T1` reads `y`, it may see an inconsistent state, and therefore produce an inconsistent state as output. In terms of histories, we have the anomaly: `A5A: r1[x]...w2[x]...w2[y]...c2...r1[y]...(c1 or a1)`.
    + `A5B` (Write Skew). Suppose `T1` reads `x` and `y`, which are consistent with `C()`, and then a `T2` reads `x` and `y`, writes `x`, and commits. Then `T1` writes `y`. If there were a constraint between `x` and `y`, it might be violated. In terms of histories, we have the anomaly: `A5B: r1[x]...r2[y]...w1[y]...w2[x]...(c1 and c2 occur)`.
  + Clearly neither `A5A` nor `A5B` could arise in histories where `P2: r1[x]...w2[x]...((c1 or a1) and (c2 or a2) in any order)` is precluded, since both `A5A` and `A5B` have `T2` write a data item that has been previously read by an uncommitted `T1`. Thus, phenomena `A5A` and `A5B` are only useful for distinguishing isolation levels that are below REPEATABLE READ in strength.
+ Snapshot Isolation cannot experience the `A3: r1[P]...w2[y in P]...c2...r1[P]...c1` anomaly. A transaction reading a predicate after an update by another will always see the same old set of data items. But the REPEATABLE READ isolation level can experience `A3` anomalies. Therefore REPEATABLE READ admits history anomalies that Snapshot Isolation does not.

#### Remark 10: ANOMALY SERIALIZABLE << SNAPSHOT ISOLATION

Snapshot Isolation histories preclude anomalies `A1`, `A2` and `A3`. Therefore, in the anomaly interpretation of ANOMALY SERIALIZABLE of Table 1: ANOMALY SERIALIZABLE << SNAPSHOT ISOLATION.

### Snapshot Isolation's benefits

Snapshot Isolation's benefits for update transactions is still debated. It probably isn’t good for long-running update transactions competing with high-contention short transactions, since the long-running transactions are unlikely to be the first writer of everything they write, and so will probably be aborted. (e.g., Start-Timestamp-1, Start-Timestamp-2, Commit-Timestamp-2, Start-Timestamp-1).

### Table 4.2. Enhanced ANSI SQL Isolation Levels Defined in terms of the eight phenomena

| Isolation Level                  | `P0`<br/>Dirty Write | `P1`<br/>Dirty Read | `P4C`<br/>Cursor Lost Update | `P4`<br/>Lost Update | `P2`<br/>Fuzzy Read | `P3`<br/>Phantom                                                  | `A5A`<br/>Read Skew | `A5B`<br/>Write Skew |
| -------------------------------- | -------------------- | ------------------- | ---------------------------- | -------------------- | ------------------- | ----------------------------------------------------------------- | ------------------- | -------------------- |
| READ UNCOMMITTED<br/>== Degree 1 | Not Possible         | Possible            | Possible                     | Possible             | Possible            | Possible                                                          | Possible            | Possible             |
| READ COMMITTED<br/>== Degree 2   | Not Possible         | Not Possible        | Possible                     | Possible             | Possible            | Possible                                                          | Possible            | Possible             |
| Cursor Stability                 | Not Possible         | Not Possible        | Not Possible                 | Sometimes Possible   | Sometimes Possible  | Possible                                                          | Possible            | Sometimes Possible   |
| REPEATABLE READ                  | Not Possible         | Not Possible        | Not Possible                 | Not Possible         | Not Possible        | Possible                                                          | Not Possible        | Not Possible         |
| Snapshot                         | Not Possible         | Not Possible        | Not Possible                 | Not Possible         | Not Possible        | Sometimes Possible (Why? A3 is not possible, but P3 is possible?) | Not Possible        | Possible             |
| SERIALIZABLE<br/>== Degree 3     | Not Possible         | Not Possible        | Not Possible                 | Not Possible         | Not Possible        | Not Possible                                                      | Not Possible        | Not Possible         |

Why use the term "**Sometimes Possible**" other than "**Possible**" to describe the relationship between `A5B` and Cursor Stability? My understanding is: Snapshot Isolation rejects history `rc1[x]...w2[x]...w1[y]...c1`, so users can avoid Write Skew by using Cursor and FETCH as follows:

```sql
DECLARE curX CURSOR FOR SELECT value FROM <table> WHERE value IS x;
OPEN curX;
FETCH curX INTO valueX;
Update <table> SET value = y' WHERE value IS y;
CLOSE curX;
```

But Write Skew can still happen if users don't use Cursor and FETCH correctly.

## Other Multi-Version Systems

# Reference

+ [A Critique of ANSI SQL Isolation Levels, by Hal Berenson, Phil Bernstein, Jim Gray, Jim Melton, Elizabeth O'Neil and Patrick O'Neil](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-95-51.pdf)
+ [Granularity of Locks and Degrees of Consistency in a Shared Data Base, by J.N. Gray, R.A. Lorie, G.R. Putzolu and I.L. Traiger](https://web.stanford.edu/class/cs245/readings/granularity-of-locks.pdf)
+ [Concurrency Control and Recovery in Database Systems, by Philip Bernstein, Vassos Hadzilacos and Nathan Goodman](https://www.amazon.com/Concurrency-Control-Recovery-Database-Systems/dp/0201107155)
+ [Transaction Processing: Concepts and Technique, by Jim Gray and Andreas Reuter](https://dl.acm.org/doi/10.5555/573304)
+ [MySQL Tutorial: MySQL Cursor](https://www.mysqltutorial.org/mysql-cursor/)
