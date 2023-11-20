---
layout: post
title: Paper Interpretation - CEP-15 - Fast General Purpose Transactions
date: 2023-10-04 12:00:00
categories:
  - [Computer Science, Consensus]
math: true
---

## Assuming a Designer's Lens: The Journey from Fast Paxos to Accord

Imagining the design process of the Accord protocol can be both intriguing and beneficial for understanding its intricate workings. I intend to begin with the foundational elements of the [Fast Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf) protocol, and progressively build the Accord protocol, step by step.

Let's set aside the dependency relations recorded in the $deps$ field for a moment. Each transaction has a unique execution timestamp, which is used to determine the total order of conflicting transactions. Consequently, Accord should simultaneously determine both the value proposed by the user and the corresponding execution timestamp.

An obvious method for generating execution timestamps is to select a number randomly, and for replicas to simply accept this random execution timestamp. However, this approach fails to meet the requirement of deciding the total order of conflicting transactions. This requirement can be expressed as follows: at least one replica should witness transactions that may commit with smaller execution timestamps. This enables the replica to notify others: "You should wait for transaction $\gamma$ that may commit with execution timestamp $t_\gamma$ (where $t_\gamma < t_\tau$) before executing $\tau$". More formally, this is known as dependency safety: Any coordinator committing $\tau$ with $t_\tau$ does so with $\text{deps}_\tau$ containing all conflicting $\gamma$ that may be committed with $t_\gamma < t_\tau$.

To meet this requirement, we need to introduce an additional constraint for each replica: Each replica should not vote for $\tau$ if it discovers another transaction $\gamma$ that may be committed with $t_\gamma$ (where $t_\gamma < t_\tau$) and it lacks information about $\gamma$ when sending an "ok" response to $\tau$ during a previous $PreAccept$ or $Accept$ phase. By incorporating this constraint, we can fit fast rounds, slow rounds, and coordinator recovery from Fast Paxos into the $PreAccept$ phase of the consensus protocol, the $Accept$ phase of the consensus protocol, and the recovery protocol of Accord. (Uncoordinated recovery in Fast Paxos does not have a corresponding protocol in Accord). At this point, we can demonstrate that the properties of the Accord protocol (e.g., two successful ballots decide the same value, any ballots after the successful ballot should only propose the successful voted value) are equivalent to those of the Fast Paxos protocol, and the proof of correctness is similar to that of Fast Paxos.

Finally, we can envision a query dependencies protocol after the transaction $\tau$ is committed. This query requires responses from at least a fast quorum size or a slow quorum size of replicas that voted for that value. The responses are merged to generate the final dependency relations. Of course, merging responses from more replicas won't affect the correctness of the dependency relations, even if the dependency relations increase, because they only contain redundant dependency relations. Lastly, for efficiency, we combine the query response with the phase 2b ($PreAcceptReply$) message of the fast round (fast path), and this gives us the Accord protocol.

### Aligning the Terminologies

In order to facilitate a comprehensive understanding of the concepts discussed in "The Part-Time Parliament", "Fast Paxos", and this paper, it's important to note that each of these papers employs a unique set of terminology. This might pose a challenge for readers transitioning between the three. To alleviate this, I have compiled a comparative table that aligns the terminologies from all three resources.

| The Part-Time Parliament                                          | Fast Paxos (Classic Round) | CEP-15                                             |
| :-                                                                | :-                         | :-                                                 |
| ballot                                                            | round                      | ballot                                             |
| $\operatorname{nextBal}(p)$                                       | $\operatorname{rnd}(a)$    | ${MaxBallot}_\tau$                                 |
| ${\operatorname{prevVote}(p)}_{bal}$                              | $\operatorname{vrnd}(a)$   | ${AcceptedBallot}_\tau$                            |
| ${\operatorname{prevVote}(p)}_{dec}$                              | $\operatorname{vval}(a)$   | $t_\tau$ or $p.t$                                  |
| $\operatorname{lastTried}(p)$                                     | $\operatorname{crnd}(c)$   |                                                    |
|                                                                   | $\operatorname{cval}(c)$   |                                                    |
| Step 1 of the Basic Protocol                                      | phase 1a                   | Recovery Protocol                                  |
| $\operatorname{NextBallot}(b)$                                    | phase 1a message           | $Recover(b, \tau, t_0)$                            |
| Step 2 of the Basic Protocol                                      | phase 1b                   | Recovery Protocol                                  |
| $\operatorname{LastVote}(b, v)$                                   | phase 1b message           | $RecoverOK(*, Superseding, Wait)$                  |
| Step 3 of the Basic Protocol                                      | phase 2a                   | Recovery Protocol                                  |
| $\operatorname{BeginBallot}(b, d)$                                | phase 2a message           | $Accept(b, \tau, {t_0}_\tau, t_\tau, {deps}_\tau)$ |
| Step 4 of the Basic Protocol                                      | phase 2b                   | Recovery Protocol                                  |
| $\operatorname{Voted}(b, q)$                                      | phase 2b message           | $AcceptOK(deps)$                                   |
|                                                                   | CP                         |                                                    |
| Theorem 1 in the "A Formal Statement of Three Conditions" section |                            |                                                    |

| Fast Paxos (Fast Round) | CEP-15                                                                                                              |
| :-                      | :-                                                                                                                  |
| any message             |                                                                                                                     |
| phase 2a                | $PreAccept(\tau, t_0)$                                                                                              |
| phase 2a message        | Consensus Protocol                                                                                                  |
| phase 2b                | $PreAcceptOK\left(t_\tau, deps:\left\{\gamma \mid \gamma \sim \tau \wedge t_{0_\gamma} < t_{0_\tau}\right\}\right)$ |
| phase 2b message        | Consensus Protocol                                                                                                  |

The original paper omits numerous details, leading me to inductively infer some information. For instance, consider the column containing ${\operatorname{prevVote}(p)}_{dec}$ which corresponds to $t_\tau$ or $p.t$ in the first table; the paper does not explicitly state that each replica should record the timestamp $t_\tau$ from $PreAccept(\tau, t_0)$ or $Accept(b, \tau, {t_0}_\tau, t_\tau, {deps}_\tau)$ requests prior to responding with $PreAcceptOK$ or $AcceptOK$ messages. However, this recording is necessary, as seen in the following procedure:

![Full Protocol Specification, Algorithm 7, the RecoverOK Phase](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-4-receive-acceptok.png)

Upon receiving a $RecoverOK(*, Superseding, Wait)$ message, the replica uses $p.t$ from $p$ with the highest ${AcceptedBallot}_\tau$ as the value to run the next $Accept$ phase. I believe that each acceptor should record the timestamp $t_\tau$ from $PreAccept(\tau, t_0)$ or $Accept(b, \tau, {t_0}_\tau, t_\tau, {deps}_\tau)$ requests, and include them in the subsequent $RecoverOK(*, Superseding, Wait)$ message.

### Augmenting Fast Paxos for Ensuring Dependency Safety

> **Property 3.3** (Dependency safety). Any coordinator committing $\tau$ with $t_\tau$ does so with ${deps}_\tau$ containing all conflicting $\gamma$ that may be committed with $t_\gamma < t_\tau$.

Before enhancing Fast Paxos to ensure dependency safety, it's crucial to define precisely when a value-timestamp pair (transaction) is considered decided (committed). According to the paper [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf), a quorum $Q$ is defined as a non-empty subset of servers. If all servers within this subset have the same (non-nil) value $v$ in the same register, then $v$ is said to be decided. To put it in a more familiar context based on this paper: a value-timestamp pair (transaction) is considered committed at the moment it is pre-accepted or accepted by a quorum of servers.

propose time = happens before?

With a precise definition of when a value-timestamp pair (transaction) is considered committed, we can now define the "happens before" relationship: $\tau$ is said to "happen before" $\gamma$, denoted as $\tau \xrightarrow{\text{hb}} \gamma$, if the moment at which $\tau$ is committed **precedes** the moment when $\gamma$ is committed. Importantly, the "happens before" relation does not correlate with timestamps, as demonstrated by the following table:

|                     | $\tau \xrightarrow{\text{hb}} \gamma$ | $\tau \xleftarrow{\text{hb}} \gamma$ |
| :-                  | :-                                    | :-                                   |
| $t_\tau < t_\gamma$ |                                       |                                      |
| $t_\tau > t_\gamma$ |                                       |                                      |

Two out of the four cases can be easily addressed:

+ If transaction $\tau$ happens after transaction $\gamma$, it should observe $\gamma$. Formally, this is represented as $\left(\tau \xleftarrow{\text{hb}} \gamma\right) \Rightarrow \left(\gamma \in {deps}_\tau\right)$. Furthermore, if $t_\tau > t_\gamma$, dependency safety is satisfied without any additional measures.
+ Similarly, if transaction $\gamma$ happens after transaction $\tau$, it should observe $\tau$. Formally, this is represented as $\left(\tau \xrightarrow{\text{hb}} \gamma\right) \Rightarrow \left(\tau \in {deps}_\gamma\right)$. Furthermore, if $t_\tau < t_\gamma$, dependency safety is satisfied without any additional measures.

|                     | $\tau \xrightarrow{\text{hb}} \gamma$ | $\tau \xleftarrow{\text{hb}} \gamma$ |
| :-                  | :-                                    | :-                                   |
| $t_\tau < t_\gamma$ | Without any additional measures.      |                                      |
| $t_\tau > t_\gamma$ |                                       | Without any additional measures.     |

The other two cases are comparatively more complex. Generally, two potential strategies can be considered:

+ One direct strategy is to instruct replicas to **deny voting** for $\tau$ if they identify a violation in dependency safety. In other words, $\gamma$ with $\left(t_\gamma > t_\tau\right) \wedge \left(\tau \notin {deps}_\gamma\right)$ effectively **fences** $\tau$ (we'll refer to this as a **transaction-fence**; this is in contrast to "A Generalised Solution to Distributed Consensus", which uses nil to prevent the register from being written a value, a concept we'll term as a **ballot-fence**). However, according to "A Generalised Solution to Distributed Consensus", Paxos is not designed to have unwritten registers deny values. Furthermore, this method could potentially disrupt the progress requirement. It's important to underscore that I'm not entirely certain, but there's a possibility that the values required by dependency safety from the current paper and Theorem 1 from "The Part-Time Parliament" may differ.
+ An alternative strategy, which aligns more closely with the design pattern of Paxos, is to force the coordinator to take he responsibility to make sure ,select a value-timestamp pair that satisfies dependency safety. Put simply, maintaining dependency safety is the responsibility of the transaction that is committed later. In other words, if transaction $\tau$ happens after transaction $\gamma$ (denoted as $\tau \xleftarrow{\text{hb}} \gamma$), it falls upon the coordinator that proposes $\tau$ to ensure that it does not propose $\tau$ with a timestamp $t_\tau$ where $t_\tau < t_\gamma$ and $\tau \notin {deps}_\gamma$, as this would lead to a violation of dependency safety for $\gamma$.

Adopting the second strategy, we can address the case where $\left(\tau \xleftarrow{\text{hb}} \gamma\right) \wedge \left(t_\tau < t_\gamma\right)$ as follows:

+ If the coordinator can confirm that $\gamma$ is committed, and that $t_\tau < t_\gamma$ and $\tau \notin {deps}_\gamma$, then the coordinator should propose $\tau$ with a larger timestamp.
+ If the coordinator find $\gamma$ is ${Accepted}_\gamma$ with $t_\tau < {t_0}_\gamma$ and $\tau \notin {deps}_\gamma$, then $\gamma$ either is already committed with timestamp ${t_0}_\gamma$ or will be committed with $t_\gamma$ ($t_\gamma \lt {t_0}_\gamma$), so the coordinator should propose $\tau$ with a larger timestamp.
+ If the coordinator find $\gamma$ is ${Accepted}_\gamma$ with $t_\tau > {t_0}_\gamma$, then the coordinator is in dilemma. There are two possible cases: $\gamma$ will be committed with ${t_0}_\gamma$ in future (remember $\tau$ does not fence, we called instance fence); or $\gamma$ will be committed with $t_\gamma$ ($t_\gamma > t_\tau$) in future. If the coordinator propose $\tau$ with $t_\tau$, it may cause $\gamma$ violating dependency safety; if the coordinator propose $\tau$ with a larger timestamp, it may violates our wish: we should keep timestamp as small as possible.

贴一张 recovery protocol 的图在这里
如果 gamma 在之后 commit ，那 gamma 自然知道 tau ；但是就怕 gamma 已经 commit 过了，但 tau 不知道这件事。

不妨想象 deps 是在 commit 的那一刻算出来的，算 deps 和 commit 是一个原子动作。

Rule: propose 的时候就要保证不会破坏可能已经 commit 的 transactions

分别推导一下 slow path + slow path 的场景、slow path + recovery path 的场景，他们都符合 solution 2 的预期

## Uncovering Details: A Comparative Study of Protocol Specification and Code Implementation

### Algorithm 4: Consensus Protocol

#### The PreAccept Phase

![Full Protocol Specification, Algorithm 4, the PreAccept Phase](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-4-the-preaccept-phase.png)

The following implementation code aligns with the $PreAccept$ phase of the fast path, as outlined in the preceding protocol specification. In this stage, the coordinator sends the $PreAccept$ message, which is triggered by a user's request. This action initiates a sequence of calls starting with [`Node::coordinate`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Node.java#L213), followed by [`Coordinate::execute`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/coordinate/Coordinate.java#L30), and finally [`Agree::Agree`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/coordinate/Agree.java#L60).

It is interesting to notice that the [`TxnId`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/txn/TxnId.java#L5) is a subclass of the [`Timestamp`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/txn/Timestamp.java#L5) class, which is comprised of three members: `real`, `logical`, and `node`. These members correspond to $\text{now}$, $0$, $C$ respectively, as defined in the first line of the protocol specification $t_0 \leftarrow (\text{now}, 0, C)$. (Please note, we are omitting $Epoch$ for the purposes of this discussion). The method [`Node::uniqueNow`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Node.java#L109) generates a `Timestamp` using a methodology that differs from the one described in the original paper:

```java
public Timestamp uniqueNow() {
  return now.updateAndGet(cur -> {
    // TODO: this diverges from proof; either show isomorphism or make consistent
    long now = nowSupplier.getAsLong();
    if (now > cur.real) return new Timestamp(now, 0, id);
    else return new Timestamp(cur.real, cur.logical + 1, id);
  });
}
```

Upon receipt of a $PreAccept$ message, the [`Node::receive`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Node.java#L250) function is invoked which subsequently calls the [`PreAccept::process`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/messages/PreAccept.java#L33) function. This then triggers the [`Command::witness`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Command.java#L104) function, culminating in either a `PreAcceptNack` or `PreAcceptOk` response being sent back to the coordinator. This code incorporates several complex concepts such as instance (suggesting that a node may contain multiple instances) and shards. However, these are currently omitted for the sake of simplicity. The simplified code is provided below:

```java
public void process(Node node, Id from, long messageId) {
  Instance instance = txn.local(node);
  Command command = instance.command(txnId);
  if (command.promised.compareTo(Ballot.ZERO) > 0) {
    node.reply(from, messageId, PreAcceptNack.INSTANCE);
  } else {
    if (!command.hasBeen(PreAccepted)) {
      Timestamp max = txn.maxConflict(instance);
      // unlike in the Accord paper, we partition shards within a node,
      // so that to ensure a total order we must either:
      //  - use a global logical clock to issue new timestamps; or
      //  - assign each shard _and_ process a unique id, and use both as components of the timestamp
      Timestamp witnessed = txnId.compareTo(max) > 0 ? txnId : instance.node().uniqueNow(max);
      command.txn = txn;
      command.executeAt = witnessed;
      command.status = PreAccepted;
    }
    node.reply(from, messageId,
      new PreAcceptOk(
        command.executeAt(),
        calculateDeps(instance, txnId, txn, txnId)));
  }
}
```

The code utilizes the [`Command`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Command.java#L23) class to store fields relevant to the protocol specification. The `promised` field corresponds to ${MaxBallot}_\tau$, the `status` field can represent various states such as ${PreAccepted}_\tau$, ${Accepted}_\tau$, ${Committed}_\tau$, among others. The `txnId` field corresponds to ${t_0}_\tau$, and `executeAt` corresponds to $t_\tau$.

```java
class Command {
  private final TxnId txnId;
  private Ballot promised = Ballot.ZERO, accepted = Ballot.ZERO;
  private Timestamp executeAt;
  private Dependencies deps = new Dependencies();
  private Status status = NotWitnessed;
```

#### Upon Receipt of the $PreAcceptOK$ Message

![Full Protocol Specification, Algorithm 4, receive PreAcceptOK](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-4-receive-preacceptok.png)

When a $PreAcceptOK$ message is received, the [`Agree::onPreAccept`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/coordinate/Agree.java#L92) function is invoked. This function implements the protocol specifications outlined above:

```java
private synchronized void onPreAccept(Id from, PreAcceptReply receive) {
  PreAcceptOk ok = (PreAcceptOk) receive;
  preAcceptOks.add(ok);
  boolean fastPath = ok.witnessedAt.compareTo(txnId) == 0;
  if (fastPath && fastPathElectorate.contains(from) &&
      ++fastPathPreAccepts == fastPathQuorumSize) {
    ++fastPathAccepted;
  }
  if (++preAccepts == slowPathQuorumSize) {
    ++preAccepted;
  }
  if (fastPathAccepted == 1) {
    // isFastPathAccepted
    preacceptOutcome = PreacceptOutcome.COMMIT;
    Dependencies deps = new Dependencies();
    for (PreAcceptOk preAcceptOk : preAcceptOks) {
      if (preAcceptOk.witnessedAt.equals(txnId)) {
        deps.addAll(preAcceptOk.deps);
      }
    }
    agreed(txnId, deps);
  } else if (preAccepted == 1) {
    // shouldSlowPathAccept
    preacceptOutcome = PreacceptOutcome.ACCEPT;
    Timestamp executeAt = Timestamp.NONE;
    Dependencies deps = new Dependencies();
    for (PreAcceptOk preAcceptOk : preAcceptOks) {
      deps.addAll(preAcceptOk.deps);
      executeAt = Timestamp.max(executeAt, preAcceptOk.witnessedAt);
    }
    startAccept(executeAt, deps);
  }
}
```

#### Upon Receipt of the $Accept$ Message

![Full Protocol Specification, Algorithm 4, receive Accept](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-4-receive-accept.png)

The methods [`Accept::process`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/messages/Accept.java#L32) and [`Command::accept`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/local/Command.java#L135) are the key functions that implement the partial protocol specification delineated from lines 27 to 37. To streamline the implementation, I have consolidated `Command::accept` into `Accept::process`.

```java
public void process(Node on, Node.Id replyToNode, long replyToMessage) {
  Instance instance = txn.local(on);
  Command command = instance.command(txnId);
  if (command.promised.compareTo(ballot) > 0) {
    on.reply(replyToNode, replyToMessage, new AcceptNack(command.promised()));
  } else if (hasBeen(Committed)) {
    on.reply(replyToNode, replyToMessage, new AcceptNack(command.promised()));
  } else {
    command.promised = command.accepted = ballot;
    command.executeAt = executeAt;
    command.status = Accepted;
    command.deps = deps;
    command.witness(txn);
    on.reply(replyToNode,
             replyToMessage,
             new AcceptOk(calculateDeps(instance, txnId, txn, executeAt)));
  }
}
```

The line `command.promised = command.accepted = ballot` corresponds to ${MaxBallot}_\tau \leftarrow b$ and ${AcceptedBallot}_\tau \leftarrow b$. Meanwhile, `command.executeAt = executeAt` corresponds to the assignment of the timestamp $t_\tau$. This implementation fulfills one of the detailed requirements specified between lines 34 and 35 of the protocol: the replica must record the timestamp from the $Accept$ message. This modification enhances the protocol's resemblance to Fast Paxos, thereby simplifying comprehension and proving correctness. The statement `command.status = Accepted` aligns with ${Accepted}_\tau \leftarrow true$. A critical step not mentioned in the prior protocol specification is `command.deps = deps`, which becomes essential when proving the correctness of the recovery protocol, a topic that will be explored in greater detail later in this blog post.

> For any $v$ committed on the slow path, an $Accept$ or $Commit$ must be witnessed by $\mathcal{R}^\tau$ so that we may inspect ${deps}_v$. If ${Accepted}_v$, $v$ must have reached a simple quorum $Q^v$ during $PreAccept$ before proposing ${deps}_v$, so that if $\tau \notin {deps}_v$ and ${t_0}_v > {t_0}_\tau$ we know that **$\tau$ could not have reached fast-path consensus** and we may proceed on the slow path. Similarly, if ${Committed}_v$, $v$ must have reached $Q^v$ during $Accept$ so we may test $t_v > {t_0}_\tau \wedge \tau \notin {deps}_v$.

#### Upon Receipt of the $AcceptOK$ Message

![Full Protocol Specification, Algorithm 4, receive AcceptOK](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-4-receive-acceptok.png)

The methods [`AcceptPhase::onAccept`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/coordinate/AcceptPhase.java#L69) and [`AcceptPhase::onAccepted`](https://github.com/apache/cassandra-accord/blob/93533f5f701dfff084f7db08a0a55e64bb7f3651/accord-core/src/main/java/accord/coordinate/AcceptPhase.java#L91) are the key functions that implement the partial protocol specification delineated from lines 39 to 41. To streamline the implementation, I have consolidated `AcceptPhase::onAccept` into `AcceptPhase::onAccepted`.

```java
private void onAccept(Id from, AcceptReply reply) {
  AcceptOk ok = (AcceptOk) reply;
  acceptOks.add(ok);
  if (++accepts == slowPathQuorumSize) {
    Dependencies deps = new Dependencies();
    for (AcceptOk acceptOk : acceptOks) {
      deps.addAll(acceptOk.deps);
    }
    agreed(proposed, deps);
  }
}
```

The condition "receive $AcceptOK(deps)$ on $C$ from $Q_{t_0}^\tau \cup Q_t^\tau$" is ambiguous. This could be interpreted as "some nodes from $Q_{t_0}^\tau \cup Q_t^\tau$" or "every node from $Q_{t_0}^\tau \cup Q_t^\tau$". However, the code provides clarity on this matter. Furthermore, the implementation in the code aligns more closely with Fast Paxos, which stipulates that the number of phase 2b messages must equal the number of phase 2a messages.

### Algorithm 7: Recovery Protocol

![Full Protocol Specification, Algorithm 7, set superseding upon receipt of the Recover message](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-7-set-superseding-upon-receipt-of-the-recover-message.png)

![Full Protocol Specification, Algorithm 7, when p.superseding is not empty](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/paper-interpretation-cep-15-fast-general-purpose-transactions/full-protocol-specification-algorithm-7-when-p-superseding-is-not-empty.png)

+ Lines 21 to 30 handle the case where $\tau$ has been committed on the slow path. If the replica goes through these lines, then $\tau$ could not have been committed on the slow paths.
+ Lines 33 to 34 handle the case where $\tau$ could not have been committed on the fast path. In the recovery process, we could propose $t_0$ again, but it's unlikely to be accepted. Instead, we propose $\operatorname{max}(p.t \mid p \in \mathcal{R}^\tau)$, which has the highest likelihood of acceptance.
+ In the recovery process for an incomplete transaction $\tau$, which neither could have been committed on the fast path nor on the slow path, we have the flexibility to propose any timestamp while preserving the safety (correctness) of the algorithm. However, two specific values, $t_0$ and $\operatorname{max}(p.t \mid p \in \mathcal{R}^\tau)$, are more logical choices than other timestamps. I believe the author's intent is to guide the recovery protocol towards proposing $t_0$ whenever feasible. Only when $t_0$ is conclusively deemed unacceptable, does the recovery protocol shift to propose $\operatorname{max}(p.t \mid p \in \mathcal{R}^\tau)$ in order to maximize the likelihood of acceptance.
  + Lines 35 to 36 handle the case where there's at least one transaction $\gamma$ that may execute after $\tau$ and $\tau$ is not included in ${deps}_\gamma$ of $\gamma$. We could propose $t_0$ again in this scenario, but it's likely to be rejected. So, we propose $\operatorname{max}(p.t \mid p \in \mathcal{R}^\tau)$, which again has the highest likelihood of acceptance.
  + > This leaves only those transactions $\gamma$ where ${t_0}_\gamma < {t_0}_\tau$ that may have reached slow-path consensus with $t_\gamma > {t_0}_\tau$ but have not been committed. Such transactions may not have witnessed $\tau$ without prohibiting $\tau$ from reaching fast-path consensus. If we have not determined the correct course of action by other means, we may simply wait for these transactions to commit, or commit them ourselves.

两个目标：
1. 同一个 instance 的两次成功的 ballots 只能投同一个 timestamp
2. 两个 instance 的结果要建立正确的依赖关系 <- 如果依赖关系不正确，直接拒绝投票（ accept/preaccept 都这么处理）
但是 accept 是没有拒绝的，要注意 classical paxos 也是这么设计的：在写入 register sets 之前要确保这个值是可以写入的，而不是交给 registers 去判断要不要写入？也不一定，扩展 fence 语义就可以做到。那为什么不扩展 fence 语义？是不是会导致死锁？同时遵循 1 和 2 会导致某个 instance 死锁，再也投不下去了。所以 accept 阶段是不能有 fence 语义的？

preaccept 就是 acceptors 在接受不同值的过程

#### Examining the Case when $p.Superseding$ is not Empty

> Fast-path recovery operates on a simple intuition: if we may deduce that an incomplete transaction $\tau$ either cannot have been committed on the fast path or that any $\gamma$ that may execute after $\tau$ has $\tau \in {deps}_\gamma$, then we may safely propose $t = t_0$ by the slow path.

\begin{aligned}
Superseding
  \leftarrow &
  \left\{
      \gamma
    \mid
             (\gamma \sim \tau)
      \wedge {Accepted}_\gamma
      \wedge ({t_0}_\gamma > {t_0}_\tau)
      \wedge (\tau \notin {deps}_\gamma)
  \right\} \\
  \cup &
  \left\{
      \gamma
    \mid
             (\gamma \sim \tau)
      \wedge {Committed}_\gamma
      \wedge (t_\gamma > {t_0}_\tau)
      \wedge (\tau \notin {deps}_\gamma)
  \right\}
\end{aligned}

#### Examining the Case when $p.Wait$ is not Empty

\begin{aligned}
Wait \leftarrow
  \left\{
      \gamma
    \mid
             (\gamma \sim \tau)
      \wedge {Accepted}_\gamma
      \wedge ({t_0}_\gamma < {t_0}_\tau < t_\gamma)
      \wedge (\tau \notin {deps}_\gamma)
  \right\}
\end{aligned}

## Reference

+ [Fast Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf)
+ [A Generalised Solution to Distributed Consensus](https://arxiv.org/pdf/1902.06776.pdf)
+ [Boxuan Li: Distributed Transaction in Database: From EPaxos to Accord](https://li-boxuan.medium.com/distributed-transaction-in-database-from-epaxos-to-accord-6de7999ad08e)
