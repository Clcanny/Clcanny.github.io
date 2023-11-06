---
layout: post
title: Paper Interpretation - A Generalised Solution to Distributed Consensus
date: 2023-11-04 22:56:34
categories:
  - [Computer Science, Consensus]
math: true
---

## Introduction

This paper presents an inspiring piece of work. Creating a distributed consensus algorithm from scratch is no easy task, as Leslie Lamport, the Turing Award winner, once said: "...this consensus algorithm follows almost unavoidably from the properties we want it to satisfy." What this paper does beautifully is to demystify this process, showing even those of us who aren't Turing laureates how to design a consensus algorithm from the ground up.

Building upon the insights from this paper, I plan to revisit the proofs of classical Paxos, Flexible Paxos, and Fast Paxos. My aim is to reinterpret and understand them within the framework presented in this paper.

## Problem Definition

The classic formulation of consensus considers how to decide upon a **single** value in a distributed system. We consider systems comprised of two types of participant: servers, which store the value, and clients, which read/write the value. If you have read [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf), you'll see that the priest's role is like a mix of the server and client roles as defined in this paper. Interestingly, in most consensus literature, the server role combines the functions of both the client and server as defined here. So, when studying consensus in this context, it's best to forget the usual definitions of server and client roles and instead follow Heidi Howard's definition.

An algorithm solves consensus if it satisfies the following three requirements:

+ **Non-triviality**. All output values must have been the input value of a client.
+ **Agreement**. All clients that output a value must output the same value.
+ **Progress**. All clients must eventually output a value if the system is reliable and synchronous for a sufficient period. This requirement rules out algorithms that could reach deadlock, but it doesn't exclude those that could enter a state of livelock or become stuck when the liveness condition isn't satisfied. As termination cannot be guaranteed in an asynchronous system where failures may occur, algorithms need only guarantee termination assuming liveness.

## Single-Server Solution

![Single Server](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/single-server-1.png)

![Single Server](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/single-server-2.png)

If we have only one server, the solution is straightforward. The server has a single persistent write-once register, $R0$, to store the decided value. Clients send requests to the server with their input value. If $R0$ is unwritten, the value received is written to $R0$ and is returned to the client. If $R0$ is already written, then the value in $R0$ is read and returned to the client. The client then outputs the returned value. This algorithm achieves consensus but requires the server to be available for clients to terminate. To overcome this limitation requires deployment of more than one server, so we now consider how to generalise to multiple servers.

## Multiple Servers, Each with a Single Write-Once Persistent Register Solution

We could say a client has to write to all the registers to decide a value, but then that would be even worse than the original algorithm, because now we have three servers and if any one of the three fails, we won't be able to make progress. So let's write to a majority of servers (two or three). That means that there would be an overlap between any two majorities and if one failed, we could still reach a decision. We have got safety, which is great. Unfortunately, we **don't actually have the progress property**. So we could have a scenario like this, three clients come along, and each of these three clients talks to one of the three servers first and then we've got one register with the value $A$, one register with the value $B$, and one register with the value $C$. We said we wanted **immutability** property. We're pretty stuck now, there's nothing we can do without overwriting these registers, so we don't have progress.

![Split Votes](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/multi-server-each-with-a-sginle-register-split-votes.png)

## Multiple Servers, Each with Multiple Write-Once Persistent Registers Solution

Consider a set of servers, $\{S_0, S_1, \ldots, S_n\}$, where each has a infinite series of write-once, persistent registers, $\{R_0, R_1, \ldots, R_n\}$. Clients read and write registers on servers and, at any time, each register is in one of the three states:

+ **unwritten**, the starting state for all registers; or
+ **contains a value**, e.g., $A$, $B$, $C$; or
+ **contains nil**, a special value denoted as $\perp$.

![Multiple Servers, Each with Multiple Write-Once Persistent Registers](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/multi-server-each-with-multi-registers.png)

The following concepts need to be clarified:

+ A **quorum**, $Q$, is a (non-empty) subset of servers, such that if all servers have a same (non-nil) value $v$ in **the same register** then $v$ is said to be decided. If you're familiar with distributed systems, you might be thinking about concepts like quorums, majorities, and read-write quorums. However, for now, please set aside any ideas about the necessity for these constructs to intersect. We'll see later whether we do or do not need any intersection properties between them.
+ A **register set**, $i$, is the set comprised of the register $R_i$ from each server. Each register set $i$ is configured with a set of quorums, $\mathcal{Q}_i$, and four example configurations are given in Figure 1.
+ The state of all registers can be represented in a table, known as a **state table**, where each column represents the state of one server and each row represents a register set.

![Figure 1: Sample configurations for systems of three or four servers.](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/figure-1-sample-configurations-for-systems-of-three-or-four-servers.png)

![Figure 2: Sample state tables for a system using the configuration in Figure 1a.](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-a-generalised-solution-to-distributed-consensus/figure-2-sample-state-tables-for-a-system-using-the-configuration-in-figure-1a.png)

We define a value as being decided when we can identify at least one register set $i$, and a quorum $Q_i$ such that $Q_i \in \mathcal{Q}_i$ (where $\mathcal{Q}_i$ represents the configured quorum sets of the register set $i$), and every server in $Q_i$ has its register $R_i$ uniformly written with the identical non-nil value $v$. By combining a configuration with a state table, we can determine whether any decision(s) have been reached (indicated by the gray highlights), as shown in Figure 2.

### Correctness

The algorithm adheres to the following four rules, which in turn ensures the satisfaction of the non-triviality, agreement, and progress requirements. Fulfilling these requirements ultimately leads to the successful resolution of consensus.

+ Rule 1: **Quorum agreement**. A client may only output a (non-nil) value $v$ if it has read $v$ from a quorum of servers in the same register set. This rule ensures that clients only output values that have been decided. When combined with rules 3 and 4 (which guarantee that at most only one value can be decided), this rule ensures the fulfillment of the **agreement** requirement.
+ Rule 2: **New value**. A client may only write a (non-nil) value $v $provided that either $v$ is the client's input value or that the client has read $v$ from a register. This rule ensures the fulfillment of the **non-triviality** requirement.
+ Before a client writes a value to a register $R_i$ in register set $i$, it needs to ensure that no other values could be decided in register sets $0$ through $i$ (inclusive). The client plans to write into register $R_i$; however, it's the client's responsibility to verify that none of the previous registers could decide on a different value prior to doing so. This is a crucial step for maintaining safety. All clients must perform this check to prevent conflicting decisions.
  + Interestingly, if writing to a register $R_i$ wouldn't lead to a value being decided, then the client has the freedom to write any value of their preference. This implies that a more relaxed condition could be proposed. However, this relaxed aspect is not significant in the current context, so it is omitted.
  + Rule 3: **Current decision**. A client may only write a (non-nil) value $v$ to register $r$ on server $s$ provided that if $v$ is decided in register set $r$ by a quorum $Q \in \mathcal{Q}_r$ where $s \in Q$ then no value $v^\prime$ where $v \neq v^\prime$ can also be decided in register set $r$.
  + Rule 4: **Previous decisions**. A client may only write a (non-nil) value $v$ to register $r$ provided no value $v^\prime$ where $v \neq v^\prime$ can be decided by the quorums in register sets $0$ to $r − 1$.

Implementing rule 1 and rule 2 is straightforward. We will not delve into their details in the later sections. Instead, our focus will be on providing guidance on the correct implementation of rule 3 and rule 4.

### How the Multi-Decree Parliament Implements the Correctness Rules

[The Multi-Decree Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf) employs **disjoint quorums** to implement Rule 3, whereby all values written to a particular register set must be identical. This can be achieved by assigning register sets to clients and requiring that **clients write only to their own register sets, with at most one value**. In practice, this could be implemented by using an allocation such as that in Figure 4 and by requiring clients to keep a persistent record of which register sets they have written too. We refer to these as client **restricted configurations**.

For those familiar with [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf), a useful correspondence can be drawn between register sets in the current paper and the concept of ballots in Paxos.

那为什么 paxos 要用 highest ballot 作为 phase 2 投票的值呢？任何一个 ballot 的可以吗？
不可以
i - 1 投了 v 说明 0 -> i - 2 都要么没投，要么投了 v
i - k 投了 v 不能说明 i - 1 要么没投，要么投了 v （因为 i 只观察了部分 servers ）
highest ballot 还说明之后的 ballot 都被 fence 了，不可以投票了

fast paxos 的另一种推导 quorum 的方式：slow quorum 到底要问多少个 server ，才可以推导出唯一的 maybe v ，而不是 maybe v + maybe w ？(S 与 F1的交集）∩（s 与 F2 的交集）不是空集，所以不会给出冲突的答案。

flexible paxos ？

## Reference

+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [Distributed Consensus Revised by Heidi Howard](https://youtu.be/Pqc6X3sj6q8?feature=shared)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
