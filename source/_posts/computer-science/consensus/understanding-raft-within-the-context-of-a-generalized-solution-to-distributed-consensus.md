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

Let's conceptualize Raft as an algorithm designed to reach agreement on a single decision (analogous to The Single-Decree Synod), focusing on a single replicated log entry, rather than its full implementation that reaches agreement on a series of decisions such as a log (akin to The Multi-Decree Parliament).

Raft and Paxos employ similar methods to adhere to Rule 4. Both algorithms initially apply a "fence-and-read-majority" strategy to create a decision table consisting of all entries from terms less than $r$. Subsequently, they introduce a minor optimization: rather than assessing the entire decision table, they focus solely on identifying the highest term $k$ where $k < r$ that holds a non-nil value in the responses. Unlike Paxos, Raft ensures through its leader election algorithm that the leader possesses the entry with the highest term $k$, so the Raft paper states:

> In some consensus algorithms, such as Viewstamped Replication, a leader can be elected even if it doesn't initially contain all of the committed entries. These algorithms contain additional mechanisms to **identify the missing entries and transmit them to the new leader**, either during the election process or shortly afterwards. Unfortunately, this results in considerable additional mechanism and complexity.
>
> Raft uses a simpler approach where it guarantees that all the committed entries from previous terms are present on each new leader from the moment of its election, without the need to transfer those entries to the leader. This means that log entries only flow in **one direction**, from leaders to followers, and leaders never overwrite existing entries in their logs.

If the leader writes values to registers for term $r$, the preceding argument holds true. However, in Raft, the leader writes the value $v$ to registers of term $k$ — the highest term for which registers contain the non-nil value $v$ as determined from the responses of the fence-and-read-majority action, and where $k < r$ — instead of term $r$. This deviation challenges the premise that each register is written to only once, and the assumption that each replica's local state table will always contain a subset of the values from the global state table.

> Raft incurs this extra complexity in the commitment rules because log entries retain their original term numbers when a leader replicates entries from previous terms. In other consensus algorithms, if a new leader re-replicates entries from prior "terms," it must do so with its new "term number." Raft's approach makes it easier to reason about log entries, since they maintain the same term number over time and across logs.

Due to this deviation, Raft no longer conforms to Rule 4. To illustrate this, consider the following example from the Raft paper:

![Figure 8: A time sequence showing why a leader cannot determine commitment using log entries from older terms.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/figure-8-a-time-sequence-showing-why-a-leader-cannot-determine-commitment-using-log-entries-from-older-terms.png)

> ... At this point, the log entry from term 2 has been replicated on a majority of the servers, but it is not committed. ... However, if S1 replicates an entry from its current term on a majority of the servers before crashing, as in (e), then this entry is committed (S5 cannot win an election).

> To eliminate problems like the one in Figure 8, Raft never commits log entries from previous terms by counting replicas. **Only log entries from the leader's current term are committed by counting replicas;** once an entry from the current term has been committed in this way, then all prior entries are committed indirectly because of the Log Matching Property.

In summary, due to a minor divergence, Raft does not align with the previous decisions rule outlined in [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf). To address this problem, Raft reinterprets the criteria for commitment or decision: a value $v$ is considered decided or committed if a quorum of servers contains the same non-nil value $v$ in their registers of the **initial** register set, as opposed to having it in corresponding registers across any same register sets as required by [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf).

## Reference

+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
+ [In Search of an Understandable Consensus Algorithm](https://raft.github.io/raft.pdf)
