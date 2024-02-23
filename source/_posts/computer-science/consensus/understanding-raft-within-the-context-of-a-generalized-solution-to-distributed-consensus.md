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

In this section, I divide the content into four parts to illustrate how Raft satisfies the previous decision rule:

+ Introduction to Paxos:
  + Explain the basic process of Paxos.
  + Describe the "fence-and-read-majority" strategy.
  + Present the decision table.
+ Introduction to Raft:
  + Explain the basic process of Raft.
  + Emphasize the differences compared to Paxos.
+ Comparison of Commitment Criteria:
  + Compare the criteria for commitment or decision in Paxos and Raft.
  + Analyze why Raft requires that the committed value must be written by the corresponding leader of the register term, whereas Paxos does not.
+ Proof of Satisfaction: Adapt the proof methodology from [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf), to demonstrate that Raft also satisfies the previous decision rule.

### Introduction to Paxos

In this section, I use Paxos to refer to the Single-Decree Synod, an algorithm designed to reach agreement on a single decision. This is distinct from the Multi-Decree Parliament, which reaches agreement on a series of decisions.

#### Basic Process of Paxos

[The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf) describes the process in Section 2.3:

![The Basic Protocol of The Part-Time Parliament](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/the-basic-protocol-of-the-part-time-parliament.png)

[A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf) also describes the process in another form in Section 4:

![The Paxos Algorithm using Write-Once Registers, from A Generalised Solution to Distributed Consensus](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/the-paxos-algorithm-using-write-once-registers-from-a-generalised-solution-to-distributed-consensus.png)

#### Fence-and-Read-Majority Strategy

![An Illustration of the Fence-and-Read-Majority Strategy](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/an-illustration-of-the-fence-and-read-majority-strategy.png)

#### Decision Table

### Introduction to Raft

Let's conceptualize Raft as an algorithm designed to reach agreement on a single decision (analogous to The Single-Decree Synod), focusing on a single replicated log entry, rather than its full implementation that reaches agreement on a series of decisions such as a log (akin to The Multi-Decree Parliament).

#### Basic Process of Raft

#### Key Differences Compared to Paxos

### Comparison of Commitment Criteria

#### Commitment Criteria in Paxos vs. Raft

#### Analysis of Raft's Leader-Based Commitment Requirement

### Proof of Satisfaction

Raft and Paxos employ similar methods to adhere to Rule 4. Both algorithms initially apply a "fence-and-read-majority" strategy to create a decision table consisting of all entries from terms less than $r$. Subsequently, they introduce a minor optimization: rather than assessing the entire decision table, they focus solely on identifying the highest term $k$ where $k < r$ that holds a non-nil value in the responses. Unlike Paxos, Raft ensures through its leader election algorithm that the leader possesses the entry with the highest term $k$, so the Raft paper states:

> In some consensus algorithms, such as Viewstamped Replication, a leader can be elected even if it doesn't initially contain all of the committed entries. These algorithms contain additional mechanisms to **identify the missing entries and transmit them to the new leader**, either during the election process or shortly afterwards. Unfortunately, this results in considerable additional mechanism and complexity.
>
> Raft uses a simpler approach where it guarantees that all the committed entries from previous terms are present on each new leader from the moment of its election, without the need to transfer those entries to the leader. This means that log entries only flow in **one direction**, from leaders to followers, and leaders never overwrite existing entries in their logs.

If the leader writes values to registers for term $r$, the preceding argument holds true. However, in Raft, the leader writes the value $v$ to registers of term $k$ — the highest term for which registers contain the non-nil value $v$ as determined from the responses of the fence-and-read-majority action, and where $k < r$ — instead of term $r$. This deviation challenges the premise that each register is written to only once, and the assumption that each replica's local state table will always contain a subset of the values from the global state table.

> Raft incurs this extra complexity in the commitment rules because log entries retain their original term numbers when a leader replicates entries from previous terms. In other consensus algorithms, if a new leader re-replicates entries from prior "terms," it must do so with its new "term number." Raft's approach makes it easier to reason about log entries, since they maintain the same term number over time and across logs.

![Paxos vs. Raft Comparison](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/paxos-vs-raft-comparison.png)
// todo

According to the definition presented in [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf), a value $v$ is considered decided if a quorum $Q$ - a non-empty subset of servers, typically a majority - has the same non-nil value $v$ in the same register across all its members. As previously analyzed, in Raft, the leader commits the value $v$ to registers associated with term $k$ rather than term $r$. If we adhere to the definition of how a value $v$ is decided, this deviation results in Raft not conforming to Rule 4. To illustrate this, consider the following example from the Raft paper:

![Figure 8: A time sequence showing why a leader cannot determine commitment using log entries from older terms.](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/figure-8-a-time-sequence-showing-why-a-leader-cannot-determine-commitment-using-log-entries-from-older-terms.png)

> ... At this point, the log entry from term 2 has been replicated on a majority of the servers, but it is not committed. ... However, if S1 replicates an entry from its current term on a majority of the servers before crashing, as in (e), then this entry is committed (S5 cannot win an election).

> To eliminate problems like the one in Figure 8, Raft never commits log entries from previous terms by counting replicas. **Only log entries from the leader's current term are committed by counting replicas;** once an entry from the current term has been committed in this way, then all prior entries are committed indirectly because of the Log Matching Property.

In summary, due to a minor divergence, Raft does not align with the previous decisions rule outlined in [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf). To address this problem, Raft redefines the criteria for commitment or decision: a value $v$ is considered decided or committed if a quorum of servers contains the same non-nil value $v$ in their registers for the **current** term of the corresponding leader.

![A state table showing why a leader cannot determine commitment using log entries from older terms. (Please note that, unlike Figure 8 from the Raft paper, this figure focuses on a single log entry.)](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/understanding-raft-within-the-context-of-a-generalized-solution-to-distributed-consensus/a-state-table-showing-why-a-leader-cannot-determine-commitment-using-log-entries-from-older-terms.png)

In (a) S1 is leader partially replicates the value A at two registers of term 2. In (b) S1 crashes; S5 is elected leader for term 3 with votes from S3, S4, and itself, and replicates a different value B of one register of term 3. In (c) S5 crashes; S1 restarts, is elected leader for term 4, and continues replication. At this point, although the value A has been replicated on a majority of the register set of term 2, one of these registers is written by the leader of term 4. **Since this term number is not equal to the term number of that register, it does not contribute to the decision of committing the value A when counting replicas.** Consequently, the value A is not committed. If S1 crashes as in (d), S5 could be elected leader (with votes from S2, S3, and S4) for term 5 and overwrite the value A with its value B from term 3.

In short, **only values written to registers by a leader whose term number matches those of the registers are considered** when determining if that value is committed through counting. This clarifies the real meaning of "current" in the statement from the Raft paper:

> Only log entries from the leader's current term are committed by counting replicas.

// todo
根据这个改变，raft 遵循 raft 4 ，我们可以证明它：
fence-and-read 仍然生效

### Unpacking Raft's Deviation from Rule 4: An Insightful Analysis

Before delving into the reasons behind Raft's deviation from Rule 4, it is crucial to comprehend why Paxos adheres to this rule. This analysis draws upon insights from my previous blog, {% post_link 'Paper Interpretation - A Generalised Solution to Distributed Consensus' %}, where I provide extensive context. Below, I highlight the most critical components:

> A minor optimization is available in this procedure. Instead of calculating all decision states from $0$ to $r - 1$, the client only needs to identify the highest register set $k$ containing the non-nil value $v$ and then calculate the decision state of register set $k$. Here, "highest" means that no other registers of register sets from $k + 1$ to $r - 1$ in the response have non-nil values. The client then calculates the decision state of register set $k$.
>
> + Following Rule 4, before the client (which may not necessarily be the same client that writes the value to register set $r$) writes $v$ to register set $k$, it must have already ensured that no other value $v^\prime \neq v$ can be decided in register sets from $0$ to $k - 1$. This means it's safe for the client to write $v$ to register set $r$ without violating Rule 4 on register sets from $0$ to $k - 1$.
> + According to client-restricted configurations, it's also safe for the client to write $v$ to register set $r$ without violating Rule 4 on register set $k$.
> + Since $k$ is the highest register set and the majority of registers in register sets from $k + 1$ to $r - 1$ have been fenced (written to nil), no value can be decided in these register sets. Therefore, it's safe for the client to write $v$ to register set $r$ without violating Rule 4 on register sets from $k + 1$ to $r - 1$.

## Reference

+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
+ [In Search of an Understandable Consensus Algorithm](https://raft.github.io/raft.pdf)
