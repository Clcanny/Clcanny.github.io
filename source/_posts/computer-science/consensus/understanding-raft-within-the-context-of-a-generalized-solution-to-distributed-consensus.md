---
layout: post
title: >-
  Understanding Raft within the Context of a Generalized Solution to Distributed Consensus
date: 2024-02-02 22:56:08
categories:
  - [Computer Science, Consensus]
math: true
---

## Introduction

[A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf) introduces an abstract framework for reasoning about the correctness of consensus protocols. Within this framework, four rules are specified to ensure the protocol's correctness, with the following two being particularly crucial:

> + Before a client writes a value to a register $R_i$ in register set $i$, it needs to ensure that no other values could be decided in register sets $0$ through $i$ (inclusive). The client plans to write into register $R_i$; however, it's the client's responsibility to verify that none of the previous registers could decide on a different value prior to doing so. This is a crucial step for maintaining safety. All clients must perform this check to prevent conflicting decisions.
>   + Interestingly, if writing to a register $R_i$ wouldn't lead to a value being decided, then the client has the freedom to write any value of their preference. This implies that a more relaxed condition could be proposed. However, this relaxed aspect is not significant in the current context, so it is omitted.
>   + Rule 3: **Current decision**. A client may only write a (non-nil) value $v$ to register $r$ on server $s$ provided that if $v$ is decided in register set $r$ by a quorum $Q \in \mathcal{Q}_r$ where $s \in Q$ then no value $v^\prime$ where $v \neq v^\prime$ can also be decided in register set $r$.
>   + Rule 4: **Previous decisions**. A client may only write a (non-nil) value $v$ to register $r$ provided no value $v^\prime$ where $v \neq v^\prime$ can be decided by the quorums in register sets $0$ to $r − 1$.

I am going to understand Raft by examining how it adheres to these two critical rules.

## How Does Raft Satisfy the Current Decision Rule?

> Alternatively, we can support disjoint quorums if we require that all values written to a given register set are the same. This can be achieved by assigning register sets to clients and requiring that clients write only to their own register sets, with at most one value. In practice, this could be implemented by using an allocation such as that in Figure 4 and by requiring clients to keep a persistent record of which register sets they have written too. We refer to these as **client restricted configurations**.

In [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf), Leslie Lamport introduces the concept of a ballot number as a tuple, where each ballot number is composed of an integer and a unique identifier of a participant, referred to as a "priest". I have named this approach **preallocation** or **static allocation**, which enables client restricted configurations.

| Ballot ID                                               | Priest/Client                                     |
| :-:                                                     | :-:                                               |
| (13, $\Gamma \rho \alpha \breve{\iota}$)                | $\Gamma \rho \alpha \breve{\iota}$                |
| (15, $\Gamma \rho \alpha \breve{\iota}$)                | $\Gamma \rho \alpha \breve{\iota}$                |
| (13, $\Lambda \iota \nu \sigma \epsilon \breve{\iota}$) | $\Lambda \iota \nu \sigma \epsilon \breve{\iota}$ |
| (15, $\Lambda \iota \nu \sigma \epsilon \breve{\iota}$) | $\Lambda \iota \nu \sigma \epsilon \breve{\iota}$ |

[A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf) presents a round robin allocation mechanism for enabling client restricted configurations:

| Register | Client |
| :-:      | :-:    |
| R0       | C0     |
| R3       | C0     |
| ...      | C0     |
| R1       | C1     |
| R4       | C1     |
| ...      | C1     |
| R2       | C2     |
| R5       | C2     |
| ...      | C2     |

[In Search of an Understandable Consensus Algorithm](https://raft.github.io/raft.pdf) utilizes the **election safety** property (at most one leader can be elected in a given term) to enable client restricted configurations. This property is guaranteed through a specific electoral process: a candidate wins an election if it receives votes from a **majority** of the servers in the full cluster for the same term. Each server will vote for **at most one** candidate in a given term, on a first-come-first-served basis. The majority rule ensures that at most one candidate can win the election for a particular term. I have named this approach **dynamic allocation**.

## How Does Raft Satisfy the Previous Decisions Rule?

We aim to understand how the paper [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf) demonstrates that Paxos adheres to the previous decisions rule and to migrate the method to Raft. To approach this, we adopt several concepts:

+ Quorum: A (non-empty) subset of servers, such that if all servers have a same (non-nil) value $v$ in the same register then $v$ is said to be decided. In Raft, a quorum is constituted by any majority subset of the servers.
+ Register: A register refers to a specific slot designated for storing a log entry, identified by a term and associated with a particular server. For instance, consider a system comprising 5 terms and 3 servers, which together account for a total of 15 registers.
  + At any time, each register is in one of the three states:
    + unwritten, the starting state for all registers.
    + contains a value, e.g., A, B, C.
    + contains $\text{nil}(\text{candidateTerm})$, e.g., $\text{nil}(3)$.
  + Similar to the principle outlined in [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf), a register adheres to a write-once policy; once it has been assigned a specific value $v$, it cannot be overwritten with a different value $v^\prime$.
  + In contrast to the principle outlined in [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf), a register containing $\text{nil}(\text{candidateTerm})$ is not immutable and can be updated to store a new value $v$ when proposed by a leader whose $\text{currentTerm}$ is greater than $\text{candidateTerm}$, or it can be overwritten with a $\text{nil}(\text{candidateTerm}^\prime)$ where $\text{candidateTerm}^\prime > \text{candidateTerm}$.
+ Register Set: A collection of all corresponding registers across all servers that share the same term.
+ State Table: A representation of the state of all registers, where each column reflects the state of one server, and each row represents a register set.
+ Local State Table: Each server independently maintains their own local copy of the state table.
+ Decision Table: A utility for tracking whether decisions have been reached or could be reached by previous quorums. At any given time, each quorum is in one of four decision states:
  + $\text{Any}$: Any value could be decided by this quorum.
  + $\text{Maybe}(v)$: If this quorum reaches a decision, then value $v$ will be decided.
  + $\text{Decided}(v)$: The value $v$ has been decided by this quorum; a final state.
  + $\text{None}$: This quorum will not decide a value; a final state.

![A sample state table.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/a-sample-state-table.png)

![A sample decision table.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/a-sample-decision-table.png)

### How Does Raft with a Single Replicated Log Entry Satisfy the Previous Decisions Rule?

Let's conceptualize Raft as an algorithm designed to reach agreement on a single decision (analogous to The Single-Decree Synod), focusing on a single replicated log entry, rather than its full implementation that reaches agreement on a series of decisions such as a log (akin to The Multi-Decree Parliament).

Upholding rule 4 presents a more formidable challenge. A tool we can utilize to address this difficulty is the **decision table**. Each server's state table consistently contains a subset of the values from the global state table, which is a consequence of the registers being write-once. Consequently, each server possesses the capability to generate a decision table drawing from their individual local state table. At any given time, each **quorum** is in one of four decision states:

+ $\text{Any}$: Any value could be decided by this quorum.
+ $\text{Maybe}(v)$: If this quorum reaches a decision, then value $v$ will be decided.
+ $\text{Decided}(v)$: The value $v$ has been decided by this quorum; a final state.
+ $\text{None}$: This quorum will not decide a value; a final state.

There are numerous ways to finalize every decision state of preceding terms to end states ($\text{Decided}(v)$ and $\text{None}$). A straightforward but inefficient way is to simply wait. However, Raft employs a faster and simpler method, which I term "fence-with-candidate-term-and-read-majority". Before writing to any registers in term $r$, the candidate requests **all** servers to place a fence on the registers of terms from $0$ to $r - 1$: if a register state is either unwritten or holds a $\text{nil}(\text{candidateTerm}^\prime)$ where $\text{candidateTerm}^\prime < \text{candidateTerm}$, the server writes $\text{nil}(\text{candidateTerm})$ to it to prevent writing by previous leaders; if not, it does nothing. The server then returns the value post-fencing. It's important to note that this fence-with-candidate-term-and-read-majority is an atomic action on each server.

To simplify our discussion, we will disregard the scenario where a leader with a $\text{currentTerm}$ exceeding that of the $\text{candidateTerm}$ associated with a $\text{nil}(\text{candidateTerm})$ entry might overwrite it. This ensures that each replica's local state table will always contain a subset of the values from the global state table. Continuing from this premise, after collecting a **majority (not all)** of responses from the fence-with-candidate-term-and-read-majority action, the successfully elected candidate (leader) can create a decision table that **remains consistently aligned with the global decision table at all times**. Based on this decision table, the successfully elected candidate (leader) can then select a value while complying with Rule 4.

A minor optimization is available in this procedure. Instead of calculating all decision states from $0$ to $r - 1$, the leader only needs to identify the highest term $k$ containing the non-nil value $v$ and then calculate the decision state of term $k$. Here, "highest" means that no other registers of terms from $k + 1$ to $r - 1$ in the response have non-nil values. The leader then calculates the decision state of term $k$.

+ Following Rule 4, before the previous leader (which may not necessarily be the same leader that writes the value to term $r$) writes $v$ to term $k$, it must have already ensured that no other value $v^\prime \neq v$ can be decided in terms from $0$ to $k - 1$. This means it's safe for the current leader to write $v$ to term $r$ without violating Rule 4 on terms from $0$ to $k - 1$.
+ According to client-restricted configurations, it's also safe for the leader to write $v$ to term $r$ without violating Rule 4 on term $k$.
+ Since $k$ is the highest term and the majority of registers in terms from $k + 1$ to $r - 1$ have been fenced (written to nil), no value can be decided in these terms. Therefore, it's safe for the leader to write $v$ to term $r$ without violating Rule 4 on terms from $k + 1$ to $r - 1$.

In the Raft algorithm, Rule 4, which pertains to respecting previous decisions, is enforced through a voting protocol based on identifying the most up-to-date log entry:

+ To begin an election, a follower increments its $\text{currentTerm}$ and transitions to candidate state. It then votes for itself and issues RequestVote RPCs in parallel to each of the other servers in the cluster. A candidate wins an election if it receives votes from a majority of the servers in the full cluster for the same term.
+ A server will cast its vote for a candidate if all of the following conditions are satisfied:
  + The candidate's term, denoted as $r$, is larger than or equal to the server's $\text{currentTerm}$.
  + It has not already voted for another candidate in term $r$.
  + The candidate's log entry is at least as up-to-date as its own. The determination of which log entry is more up-to-date is made by comparing the term numbers, **the log entry with the higher term is more up-to-date**. Consequently, the successfully elected candidate (leader) will have a log entry is at least as up-to-date as any other log entries on any of the servers in that majority.
+ By integrating the two subsequent rules with the three previously mentioned rules for casting votes for candidates, the entire election process in Raft mirrors the fence-with-candidate-term-and-read-majority action described earlier.
  + All servers, including those that voted for a candidate in term $r$, adhere to the following rule: If RPC request or response contains term $\text{T} > \text{currentTerm}$, the server updates $\text{currentTerm}$ to $\text{T}$ and converts to follower. So when a server casts its vote for a candidate whose term is $r$, it must have already updated its $\text{currentTerm}$ to $r$ prior to responding to the RequestVote request associated with term $r$.
  + A follower will respond with false to an AppendEntries request if the term included in the request is less than the follower's $\text{currentTerm}$.
  + Thus the entire election process in Raft mirrors the fence-with-candidate-term-and-read-majority action described earlier. Consequently, the candidate that is successfully elected as leader can create a decision table that remains consistently aligned with the global decision table at all times. Based on this decision table, the candidate can then select a value while complying with Rule 4.

As a result, the leader for term $r$ is guaranteed to have the log entry with the highest term $k$, where $k < r$, such that no log entries with terms $k + 1$ to $r - 1$ in all RequestVote responses from the **majority** of the servers contain non-nil values. Therefore, within term $r$, the leader has the authority to propose the log entry from the highest term $k$ while complying with Rule 4. The correctness of Raft is analogous to the previously discussed section starting with "A minor optimization is available in this procedure"; for brevity, I do not repeat the details here.

Raft and Paxos employ similar methods to adhere to Rule 4. Both algorithms initially apply a "fence-and-read-majority" strategy to create a decision table consisting of all entries from terms less than $r$. Subsequently, they introduce a minor optimization: rather than assessing the entire decision table, they focus solely on identifying the highest term $k$ where $k < r$ that holds a non-nil value in the responses. Unlike Paxos, Raft ensures through its leader election algorithm that the leader possesses the entry with the highest term $k$, so the Raft paper states:

> In some consensus algorithms, such as Viewstamped Replication, a leader can be elected even if it doesn't initially contain all of the committed entries. These algorithms contain additional mechanisms to **identify the missing entries and transmit them to the new leader**, either during the election process or shortly afterwards. Unfortunately, this results in considerable additional mechanism and complexity.
>
> Raft uses a simpler approach where it guarantees that all the committed entries from previous terms are present on each new leader from the moment of its election, without the need to transfer those entries to the leader. This means that log entries only flow in **one direction**, from leaders to followers, and leaders never overwrite existing entries in their logs.

In the interest of simplifying our discussion, I initially omitted a crucial detail, opting instead for a high-level overview. However, I now intend to introduce this detail for a more comprehensive analysis. If the leader writes values to registers for term $r$, the preceding argument holds true. However, in Raft, the leader writes the value $v$ to registers of term $k$ — the highest term for which registers contain the non-nil value $v$ as determined from the responses of the fence-with-candidate-term-and-read-majority action, and where $k < r$ — instead of term $r$. This deviation challenges the premise that each register is written to only once, and the assumption that each replica's local state table will always contain a subset of the values from the global state table. We will integrate this detail into our ongoing discussion and aim to resolve these considerations in the subsequent subsection.

#### Exploring Raft's Distinctive Strategy: Does Writing to Prior-term Registers Contravene the Fence-and-Read-Majority Action?

If the leader writes values to registers for term $r$, the preceding argument holds true. However, in Raft, the leader writes the value $v$ to registers of term $k$ — the highest term for which registers contain the non-nil value $v$ as determined from the responses of the fence-with-candidate-term-and-read-majority action, and where $k < r$ — instead of term $r$. This deviation challenges the premise that each register is written to only once, and the assumption that each replica's local state table will always contain a subset of the values from the global state table.

> Raft incurs this extra complexity in the commitment rules because log entries retain their original term numbers when a leader replicates entries from previous terms. In other consensus algorithms, if a new leader re-replicates entries from prior "terms," it must do so with its new "term number." Raft's approach makes it easier to reason about log entries, since they maintain the same term number over time and across logs.

Consider the following example:

![An example where the final decision table changes against expectations.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/an-example-where-the-final-decision-table-changes-against-expectations.png)

The initial state is such that the register of term $1$ in server $s3$ is written with $v$, while other registers remain unwritten. The sequence of events is as follows:

1. Server $s2$ initiates an election, increments its $\text{currentTerm}$ to $2$, and votes for itself.
2. Server $s2$ sends `RequestVote(term=2, candidateId=s2)` RPCs to servers $s1$ and $s3$.
3. Server $s1$ grants its vote for $s2$, and $s3$ also votes for $s2$, although $s2$ does not receive $s3$'s vote.
4. Server $s2$ receives votes from a majority, specifically from servers $s1$ and $s2$, and thus becomes leader. Given the absence of any non-nil values in the `RequestVote` RPC responses, it is free to propose any value. Assuming it opts for $v^\prime$, where $v^\prime \neq v$, $s2$ then appends $v^\prime$ to its local log. The decision table observed by $s2$ at this moment is outlined below.
5. Server $s2$ sends `AppendEntries(term=2, entries=[(command=v', term=2)])` RPC to $s1$.
6. Server $s3$ initiates an election, increments its $\text{currentTerm}$ to $3$, and votes for itself.
7. Server $s3$ sends `RequestVote(term=3, candidateId=s3)` RPCs to $s1$.
8. Server $s1$ grants its vote to $s3$.
9. Server $s3$ receives votes from a majority, comprising $s1$ and $s3$, with term $1$ containing the non-nil value $v$. Consequently, $s3$ sends `AppendEntries(term=3, entries=[(command=v, term=1)])` RPC to $s1$, instructing $s1$ to write the value $v$ into the register for term $1$.
10. Server $s1$ writes the value $v$ into the register for term $1$. This action establishes $v$ as the decided value by the quorum consisting of servers $s1$ and $s3$ for the register set of term $1$. It's crucial to note that the decision table acquired by $s2$ in step 4 now conflicts with the current decision table.

![A comparison of server s2's local decision table with the global decision table during conflict.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/a-comparison-of-server-s2-s-local-decision-table-with-the-global-decision-table-during-conflict.png)

At step 10, server $s1$ replaces a previously $\text{nil}(2)$ entry by writing the value $v$ into a register for term $1$, in response to the `AppendEntries(term=3, entries=[(command=v, term=1)])` RPC from server $s3$. This action violates the write-once assumption of registers, thereby disrupting the consistency whereby each server's local state table is a subset of the global state table. Consequently, the integrity of server $s2$'s local decision table, as derived from its local state table at step 4, is called into question. This leads to server $s2$ proposing the value $v^\prime$, which contravenes the rule of adhering to previous decisions.

However, step a will not succeed due to server $s1$ having already executed step 8, which results in its $\text{currentTerm}$ being updated to $3$. Since this term is greater than the term $2$ referenced in step a, the operation cannot be carried out. In other words, even if server $s2$ proposes the value $v^\prime$ based on an incorrect local decision table, $v^\prime$​ will not be accepted by the majority.

Generally, in the event that a future leader with a $\text{currentTerm}^\prime$ greater than the $\text{currentTerm}$ of the current leader attempts to overwrite a $\text{nil}(\text{currentTerm})$ entry, it would violate the write-once assumption of registers. Such a violation could disrupt the consistency whereby each server's local state table is a subset of the global state table. This could lead to the current leader's local decision table becoming incorrect and potentially proposing a value that might contradict previous decisions. However, this risk is mitigated by the protocol which requires the future leader to first successfully execute a fence-with-candidate-term-and-read-majority action with some majority. This preemptive step ensures that the majority will reject any `AppendEntries(currentTerm)` requests from the current leader, effectively preventing the leader from potentially writing incorrect values to a majority of the servers and making a decision. Therefore, **the fencing action by the future leader takes precedence before any overwriting occurs, and the overwriting itself precedes any changes to the decision table.** In this way, the protocol maintains consistency by ensuring that no quorum decides on a value proposed by the current leader if it is based on an outdated or incorrect state table.

## Reference

+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
+ [In Search of an Understandable Consensus Algorithm](https://raft.github.io/raft.pdf)
