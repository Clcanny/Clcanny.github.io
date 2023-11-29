---
layout: post
title: Paper Interpretation - CEP-15 - Fast General Purpose Transactions (Part 2)
date: 2023-11-29 12:00:00
categories:
  - [Computer Science, Consensus]
math: true
---

## Key Concepts and Symbols

### The Moment When Value $v$ Is Decided

According to the paper "[A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)":

> A quorum, $Q$, is a (non-empty) subset of servers, such that if all servers have a same (non-nil) value $v$ in the same register then $v$ is said to be **decided**.

To put it in a more familiar context based on this paper: a value-timestamp pair (transaction) is considered decided at the moment it is pre-accepted or accepted by a quorum of servers.

While some consensus research papers prefer to use the term "commit" instead of "decide", in the context of the current paper, "commit" carries a specific and distinct meaning. To avoid ambiguity, we opt to use "decide" in this particular discussion.

### Fast Path and Slow Path

The original paper does not provide explicit definitions for the terms "fast path" and "slow path". However, these concepts are employed in subsequent discussions. Based on these contexts, we can interpret that a value $v$ **is decided on the fast path** if it is written to all recipient replicas in a fast-path quorum $\mathcal{F}$ during the $PreAccept$ phase. Conversely, a value $v$ **is decided on the slow path** if it is written to all recipient replicas in the same ballot within a slow-path quorum $\mathcal{Q}$ during the $Accept$ phase.

> If a **fast-path** quorum of replicas unanimously accept and record this timestamp as the most recent, then only this single timestamp may be recovered and it is decided immediately. Otherwise some replicas have responded proposing newer timestamps, so that there are multiple possible Lamport timestamps that may be recovered, and therefore distinct total orders. In this case a **slow path** using classic Paxos durably agrees which of these possibilities is decided.

> Only $Accept$ may be skipped, if the **fast path** is taken.

### The Properties of the Dependency Set

> Uniquely, this dependency set is not decided consistently during consensus - only a **superset** of each transaction's final dependencies is determined, that may be filtered during execution to ensure consistency.

> $PreAccept$ and $Accept$ collectively decide the order of execution, which is durably decided prior to entry to $Commit$, where this decision is disseminated to dependent transactions.

> Once $t_\tau$ is decided it is logically committed, and disseminated to every shard alongside ${deps}_\tau$ via $Commit$ so that other transactions with an earlier execution timestamp that had witnessed us during consensus may proceed. Note that only $t_\tau$ is durably committed, ${deps}_\tau$ is only recorded for recovery purposes outlined in Section 4.

The first property to note is the determination of the dependency set for a transaction $\tau$. If the transaction is decided on the fast path, the dependency set is derived from the union of $deps$ in all $PreAcceptOK\left(t_\tau, deps:\left\{\gamma \mid \gamma \sim \tau \wedge t_{0_\gamma} < t_{0_\tau}\right\}\right)$ messages sent by the fast-path quorum $\mathcal{F}$. Conversely, if transaction $\tau$ is decided on the slow path, the dependency set is determined by the union of $deps$ in all $AcceptOK(deps)$ messages sent by the corresponding slow-quorum $\mathcal{Q}$. It is important to acknowledge that even though other types of messages may contain $deps$ fields, like the $Accept(b, \tau, {t_0}_\tau, t_\tau, {deps}_\tau)$ message, they do not contribute to the final dependency sets.

The second property to observe is that the same value-timestamp pair can be decided by different ballots across various fast-path or slow-path quorums. This can result in different dependency sets being constructed by these quorums, leading to different replicas possessing different sets of dependencies. This likely explains why the original paper underscores that "Uniquely, this dependency set is not decided consistently during consensus".

The third property worth mentioning is that even if different replicas are aware of different dependency sets, this discrepancy does not undermine the algorithm's correctness. This is because each dependency set is a **superset** of the final dependency set, and this superset is subsequently **filtered** during execution to ensure consistency. This property, where "only a superset of each transaction's final dependencies is determined," is referred to as "dependency safety" in the original paper.

> **Property 3.3** (Dependency safety). Any coordinator committing $\tau$ with $t_\tau$ does so with ${deps}_\tau$ containing all conflicting $\gamma$ that may be committed with $t_\gamma < t_\tau$.

We say that transaction $\tau$ satisfies dependency safety if $\forall \gamma, \left(\gamma \sim \tau\right) \wedge \left(t_\gamma < t_\tau\right) \Rightarrow \gamma \in {deps}_\tau$. Conversely, if $\exists \gamma, \left(\gamma \sim \tau\right) \wedge \left(t_\gamma < t_\tau\right) \wedge \left(\gamma \notin {deps}_\tau\right)$, we say that transaction $\tau$ breaches dependency safety.

### The Arrives-Before Relationship

The notation $Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)$ signifies that the $Accept(\tau)$ message arrives before the $PreAccept(\gamma)$ message at the recipient replica $P$.

Importantly, any message that has already arrived will be considered to have arrived before a message that will never arrive. Hence, we represent this as $m_a \xrightarrow{\text{ab}_P} m_{na}$, where $m_a$ is a message that has already arrived, and $m_{na}$ is a message that will never reach replica $P$. This semantics will be used later without explicit emphasis, so please bear this in mind to avoid confusion.

Employing this notation, $Recover(\tau) \xrightarrow{\text{ab}_P} PreAccept(\tau)$ denotes that the $Recover(\tau)$ message arrives at the recipient replica $P$ prior to the $PreAccept(\tau)$ message. We will refer back to this formula in the subsequent discussions.

## How Can We Prove Dependency Safety Without Involving the Recovery Protocol?

> **Property 3.3** (Dependency safety). Any coordinator committing $\tau$ with $t_\tau$ does so with ${deps}_\tau$ containing all conflicting $\gamma$ that may be committed with $t_\gamma < t_\tau$.
>
> Proof. Suppose $\tau$ is committed with $t_\tau$ and ${deps}_\tau$, and consider any $\gamma$ that commits with $t_\gamma < t_\tau$. Each of $\gamma$, $\tau$ may have committed via the slow- or fast-paths. We illustrate the case where both $\gamma, \tau$ committed via the slow-path; the other cases are similar. By assumption, $\gamma$ is pre-accepted at some slow-path quorum $\mathcal{Q}^\gamma$, where each replica in $\mathcal{Q}^\gamma$ pre-accepted $\gamma$ for some execution timestamp $\le t_\gamma$. Meanwhile, $\tau$ must be accepted at some slow-path quorum $\mathcal{Q}^\tau$ with $t_\tau$. Then for any replica $P$ in $\mathcal{Q}^\gamma \cap \mathcal{Q}^\tau$, $P$ must have pre-accepted $\gamma$ before accepting $\tau$, since otherwise $P$ will not have pre-accepted $\gamma$ with an execution timestamp less than $t_\tau$. As a result, by the Accept Phase of the protocol, $\gamma \in {deps}_\tau$.

|                                                                                                                    | $t_\tau < t_\gamma$ | $t_\tau > t_\gamma$           |
| :-                                                                                                                 | :-                  | :-                            |
| $\exists P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma, PreAccept(\gamma) \xrightarrow{\text{ab}_P} Accept(\tau)$ |                     |                               |
| $\forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma, Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)$ |                     | We should disprove this case. |

$$
\begin{align*}
&\phantom{\Rightarrow} (t_\tau > t_\gamma)
                \wedge (\forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma,
                        Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)) \\
&\Rightarrow           (t_\gamma < t_\tau)
                \wedge (\forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma,
                        Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)) \\
&\Rightarrow           (\forall P \in \mathcal{Q}^\gamma,
                        PreAccept(\gamma) \xrightarrow{\text{ab}_P} Accept(\tau))
                \wedge (\forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma,
                        Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)) \\
&\Rightarrow           (\forall P \in \mathcal{Q}^\gamma \cap \mathcal{Q}^\tau,
                        PreAccept(\gamma) \xrightarrow{\text{ab}_P} Accept(\tau))
                \wedge (\forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma,
                        Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)) \\
&\Rightarrow    \forall P \in \mathcal{Q}^\tau \cap \mathcal{Q}^\gamma,
                       (PreAccept(\gamma) \xrightarrow{\text{ab}_P} Accept(\tau))
                \wedge (Accept(\tau) \xrightarrow{\text{ab}_P} PreAccept(\gamma)) \\
&\Rightarrow \bot
\end{align*}
$$

## Case Study: The Recovery Protocol's Dilemma Under Specific Circumstances

Introducing the Recovery Protocol complexifies the scenario. Let's consider a situation where the coordinator of transaction $\tau$ receives all $RecoverOK(*_\tau, Superseding, Wait)$ messages. These messages can be divided into two sets: one set includes messages with the execution timestamp ${t_0}_\tau$, and the other includes messages with execution timestamps ${t_\tau}_P$ where ${t_\tau}_P > {t_0}_\tau$. Let's also assume the existence of another transaction $\gamma$ such that $\left(\gamma \in Accepts\right) \wedge \left({t_0}_{\gamma} \le {t_0}_\tau\right) \wedge \left(t_\gamma \lt {t_0}_\tau\right)$ in one $RecoverOK$ message's $Wait$ field. The coordinator, in this case, faces the challenge of distinguishing between two sub-cases:

### Sub-Case A: $tau$ Is Decided on the Fast Path

+ $\forall P \in F^\tau \cap Q^\gamma, PreAccept(\tau) \xrightarrow{\text{ab}_P} Accept(\gamma)$ (refer to parts "AB" and "ABC" in the Venn diagram; these recipient replicas pre-accepted ${t_0}_\tau$).
+ $\forall P \in (Q^\gamma \cap R^\tau) - F^\tau, Accept(\gamma) \xrightarrow{\text{ab}_P} Recover(\tau) \xrightarrow{\text{ab}_P} PreAccept(\tau)$ (refer to part "BC" in the Venn diagram; these recipient replicas pre-accepted an execution timestamp larger than ${t_0}_\tau$, denoted as ${t_\tau}_P$, where different replicas have different ${t_\tau}_P$).

In this sub-case, the coordinator should propose ${t_0}_\tau$ as the execution timestamp in the next $Accept$ phase of the Recovery Protocol. Failure to do so would contradict the following lemma from "[The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)":

> if a ballot $B$ in $\mathcal{B}$ is successful, then any later ballot in $\mathcal{B}$ is for the same decree as $B$, then:
>
> $$
> \forall B, B^{\prime} \in \mathcal{B}:
>     \left(
>         \left(B_{qrm} \subseteq B_{vot}\right)
>       \wedge
>         \left(B_{bal}^{\prime} > B_{bal}\right)
>     \right)
>   \Rightarrow
>     \left(B_{dec}^{\prime} = B_{dec}\right)
> $$

![Recovery Protocol Dilemma, Case A: $tau$ is decided on the fast path](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions-part-2/the-recovery-protocol-dilemma-case-a.png)

### Sub-Case B: $tau$ Is Not Decided on the Fast Path

+ $\forall P \in F^\tau \cap Q^\gamma, Accept(\gamma) \xrightarrow{\text{ab}_P} PreAccept(\tau) \xrightarrow{\text{ab}_P} Recover(\tau)$ (refer to parts "AB" and "ABC" in the Venn diagram; these recipient replicas pre-accepted an execution timestamp larger than ${t_0}_\tau$, denoted as ${t_\tau}_P$, where different replicas have different ${t_\tau}_P$).
+ $\forall P \in (F^\tau \cap R^\tau) - Q^\gamma, PreAccept(\tau) \xrightarrow{\text{ab}_P} Recover(\tau) \xrightarrow{\text{ab}_P} Accept(\gamma)$ (refer to part "AC" in the Venn diagram; these recipient replicas pre-accepted ${t_0}_\tau$).

In this sub-case, the coordinator should not propose ${t_0}_\tau$ as the execution timestamp in the next $Accept$ phase of the Recovery Protocol. Failing to do so could potentially compromise the dependency safety of transaction $\gamma$, since $\forall P \in Q^\gamma, \left(Accept(\gamma) \xrightarrow{\text{ab}_P} PreAccept(\tau)\right) \wedge \left(Accept(\gamma) \xrightarrow{\text{ab}_P} Recover(\tau)\right)$, causing transaction $\gamma$ to not witness transaction $\tau$.

> This leaves only those transactions $\gamma$ where ${t_0}_\gamma < {t_0}_\tau$ that may have reached slow-path consensus with $t_\gamma > {t_0}_\tau$ but have not been committed. Such transactions may not have witnessed $\tau$ without prohibiting $\tau$ from reaching fast-path consensus. If we have not determined the correct course of action by other means, we may simply wait for these transactions to commit, or commit them ourselves.

![Recovery Protocol Dilemma, Case B: $tau$ is not decied on the fast path](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions-part-2/the-recovery-protocol-dilemma-case-b.png)

### Unable to Distinguish Between Two Sub-Cases: Waiting as the Only Solution

From the perspective of the coordinator of transaction $\tau$, it is impossible to distinguish between sub-case A and B. Under these two sub-cases, all $RecoverOK(*_\tau, Superseding, Wait)$ messages can be divided into two sets: one set includes messages with the execution timestamp ${t_0}_\tau$, and the other includes messages with execution timestamps ${t_\tau}_P$ where ${t_\tau}_P > {t_0}_\tau$. As a result, the coordinator of transaction $\tau$ simply waits until transaction $\gamma$ is committed.

> This leaves only those transactions $\gamma$ where ${t_0}_\gamma < {t_0}_\tau$ that may have reached slow-path consensus with $t_\gamma > {t_0}_\tau$ but have not been committed. Such transactions may not have witnessed $\tau$ without prohibiting $\tau$ from reaching fast-path consensus. If we have not determined the correct course of action by other means, we may simply wait for these transactions to commit, or commit them ourselves.

## Why Doesn't the Slow Path Encounter the Dilemma Case?

In the previous section, we discussed a scenario where the Recovery Protocol faces a dilemma, compelling the coordinator of transaction $\tau$ to await the commitment of transaction $\gamma$, where ${t_0}_\gamma < {t_0}_\tau$ that may have reached slow-path consensus with $t_\gamma > {t_0}_\tau$. However, in the normal Consensus Protocol, why can the coordinator of transaction $\tau$ proceed without waiting, and initiate a new ballot with an $Accept$ message using a fresh timestamp $t_\tau > {t_0}_\tau$? The reason is that, within the standard Consensus Protocol, the coordinator is aware that transaction $\tau$ has not been decided and will not be decided on the fast path prior to proposing the new ballot on the slow path.

![Algorithm 1, Consensus Protocol](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions-part-2/algorithm-1-consensus-protocol.png)

![Quorum $\mathcal{Q}^\tau$ for Transaction $\tau$](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions-part-2/quorum-q-for-transaction-tau.png)

> $\mathcal{Q}$ represents a simple quorum. $\mathcal{Q}^\tau$ denotes a set of responses constituting a simple quorum in each replica-set in $\mathbb{P}^\tau$.

## Reference

+ [CEP-15: Fast General Purpose Transaction](https://cwiki.apache.org/confluence/display/CASSANDRA/CEP-15%3A+General+Purpose+Transactions?preview=/188744725/188744736/Accord.pdf)
+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
