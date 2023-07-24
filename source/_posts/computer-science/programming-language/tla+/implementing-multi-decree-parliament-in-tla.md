---
layout: post
title: Implementing Multi-Decree Parliament In TLA+
date: 2023-07-24 23:07:07
categories:
  - [Computer Science, Programming Language, TLA+]
---

# Spec

```tla
--------------------------- MODULE MultiDecreeParliament -------------------
\* MultiDecreeParliament.tla
EXTENDS Integers, FiniteSets, TLC
CONSTANTS PRIESTS, DECREES, INSTANCE_IDS, BALLOT_IDS
VARIABLES priestStatus, ledgers, minUnusedInstanceIds, usedBallotIds, msgs

\* Declaring symmetry during liveness checking is dangerous.
\* It might cause TLC to miss violations of the stated liveness properties.
\* Please check liveness without symmetry defined.
\* SYMM ==
\*          Permutations(PRIESTS)
\*   \union Permutations(DECREES)

InvalidInstanceId == -1
BlankBallotId == -1
BlankDecree == "BLANK"
OliveDayDecree == "The ides of February is national olive day"

NextBallotMsgType == "NextBallot"
LastVoteMsgType == "LastVote"
BeginBallotMsgType == "BeginBallot"
VotedMsgType == "Voted"
SuccessMsgType == "Success"

ASSUME
  /\ IsFiniteSet(PRIESTS)
  /\ IsFiniteSet(DECREES)
  /\ BlankDecree \notin DECREES
  /\ OliveDayDecree \notin DECREES
  /\ INSTANCE_IDS \subseteq Nat
  /\ IsFiniteSet(INSTANCE_IDS)
  /\ \A i \in INSTANCE_IDS: InvalidInstanceId < i
  /\ BALLOT_IDS \subseteq Nat
  /\ IsFiniteSet(BALLOT_IDS)
  /\ BlankBallotId \notin BALLOT_IDS

GetQuorum(ballotId, instanceId) ==
  {
    m.to:
      m \in
        {
          m \in msgs:
            /\ m.type = BeginBallotMsgType
            /\ m.ballotId = ballotId
            /\ m.decrees[instanceId] # BlankDecree
        }
  }

Init ==
  /\ priestStatus =
    [
      p \in PRIESTS |->
      [
        \* While priests can employ differing ballot IDs
        \* across various Synod instances,
        \* for the sake of simplicity, this discussion assumes that
        \* they utilize the same ballot ID
        \* each time they're selected as president.
        lastTriedBallotId |-> -1,
        prevVote          |->
          [i \in INSTANCE_IDS |-> [ballotId |-> -1, decree |-> BlankDecree]],
        nextBallotId      |-> -1
      ]
    ]
  /\ ledgers = [p \in PRIESTS |-> [i \in INSTANCE_IDS |-> BlankDecree]]
  /\ minUnusedInstanceIds = [p \in PRIESTS |-> InvalidInstanceId]
  /\ usedBallotIds = {}
  /\ msgs = {}

\* Step (1)
\* Logically, the parliamentary protocol used a separate instance of
\* the complete Synod protocol for each decree number.
\* However, a single president was selected for all these instances,
\* and he performed the first two steps of the protocol just once.
\* A newly elected president $p$ can send to some set of legislators
\* a single message that serves as the $\operatorname{NextBallot}(b)$ message
\* for all instances of the Synod protocol.
\* (There are an infinite number of instances - one for each decree number.)
SendNextBallotMsg(p) ==
  \E b \in BALLOT_IDS \ usedBallotIds:
    /\ b > priestStatus[p].lastTriedBallotId
    /\ priestStatus' = [priestStatus EXCEPT ![p].lastTriedBallotId = b]
    /\ usedBallotIds' = usedBallotIds \union {b}
    /\ msgs' = msgs \union
      {[
        type     |-> NextBallotMsgType,
        ballotId |-> b
      ]}
    /\ UNCHANGED <<ledgers, minUnusedInstanceIds>>

\* Step (2)
\* A legislator $q$ can reply with a single message that
\* serves as the LastVote messages for step 2 of
\* all instances of the Synod protocol.
\* This message contains only a finite amount of information,
\* since $q$ can have voted in only a finite number of instances.
ReceiveNextBallotMsg(q) ==
  \E b \in BALLOT_IDS:
    /\ [type |-> NextBallotMsgType, ballotId |-> b] \in msgs
    /\ b > priestStatus[q].nextBallotId
    /\ priestStatus' = [priestStatus EXCEPT ![q].nextBallotId = b]
    /\ msgs' = msgs \union {[
        type     |-> LastVoteMsgType,
        ballotId |-> b,
        vote     |-> priestStatus[q].prevVote,
        from     |-> q
      ]}
    /\ UNCHANGED <<ledgers, minUnusedInstanceIds, usedBallotIds>>

\* Step (3.1)
\* After receiving a $\operatorname{LastVote}(b, v)$ message
\* from every priest in some majority set $Q$,
\* where $b = \operatorname{lastTried}(p)$,
\* priest $p$ initiates a new ballot
\* with number $b$, quorum $Q$, and decree $d$,
\* where $d$ is chosen to satisfy $\operatorname{B3}$.
\* He then sends a $\operatorname{BeginBallot}(b, d)$ message
\* to every priest in $Q$.
ReceiveLastVoteMsg(p) ==
  \E majority \in SUBSET PRIESTS:
    LET
      b == priestStatus[p].lastTriedBallotId
      lastVoteMsgs ==
        {
          m \in msgs:
            /\ m.type = LastVoteMsgType
            /\ m.ballotId = b
            /\ m.from \in majority
        }
      maxLastVotes ==
        [
          i \in INSTANCE_IDS |->
            (CHOOSE m \in lastVoteMsgs:
              \A n \in lastVoteMsgs:
                m.vote[i].ballotId >= n.vote[i].ballotId).vote[i]
        ]
      notBlankDecreeInstanceIds ==
        {
          i \in DOMAIN maxLastVotes:
            /\ maxLastVotes[i].ballotId # BlankBallotId
            /\ maxLastVotes[i].decree # BlankDecree
        }
      maxNotBlankDecreeInstanceId ==
        IF notBlankDecreeInstanceIds = {}
          THEN InvalidInstanceId
          ELSE
            CHOOSE mid \in notBlankDecreeInstanceIds:
              \A id \in notBlankDecreeInstanceIds:
                mid >= id
      decrees ==
        [
          i \in INSTANCE_IDS |->
            IF i > maxNotBlankDecreeInstanceId
              THEN BlankDecree
              ELSE
                IF /\ maxLastVotes[i].ballotId = BlankBallotId
                   /\ maxLastVotes[i].decree = BlankDecree
                  \* Passing decrees out of order in this way might cause confusion.
                  \* In general, a new president would fill any gaps in his ledger
                  \* by passing the "olive-day" decree.
                  THEN OliveDayDecree
                  ELSE maxLastVotes[i].decree
        ]
    IN
      /\ {m \in msgs: m.type = BeginBallotMsgType /\ m.ballotId = b} = {}
      /\ {m.from: m \in lastVoteMsgs} = majority
      /\ Cardinality(majority) * 2 > Cardinality(PRIESTS)
      /\ minUnusedInstanceIds' =
        [minUnusedInstanceIds EXCEPT ![p] = maxNotBlankDecreeInstanceId + 1]
      /\ msgs' = msgs \union
        [
          type     : {BeginBallotMsgType},
          ballotId : {b},
          decrees  : {decrees},
          to       : majority
        ]
      /\ UNCHANGED <<priestStatus, ledgers, usedBallotIds>>

\* Step (3.2)
\* Then, whenever he receives a request to pass a decree,
\* he chooses the lowest-numbered decree that he is still free to choose,
\* and he performs step 3 for that decree number
\* (instance of the Synod protocol) to try to pass the decree.
SendBeginBallotMsg(p) ==
  \E d \in DECREES:
    LET
      b == priestStatus[p].lastTriedBallotId
      instanceIds == {i \in INSTANCE_IDS: i >= minUnusedInstanceIds[p]}
      instanceId ==
        IF instanceIds # {}
          THEN CHOOSE mid \in instanceIds: \A id \in instanceIds: mid <= id
          ELSE InvalidInstanceId
      decrees ==
        [i \in INSTANCE_IDS |-> IF i = instanceId THEN d ELSE BlankDecree]
    IN
      \* Ensure that Step (3.1) has been successfully completed
      \* before proceeding further.
      /\ minUnusedInstanceIds[p] # InvalidInstanceId
      \* Ensure that available instance IDs remain.
      /\ instanceId # InvalidInstanceId
      /\ minUnusedInstanceIds' =
        [minUnusedInstanceIds EXCEPT ![p] = instanceId + 1]
      /\ msgs' = msgs \union
        [
          type     : {BeginBallotMsgType},
          ballotId : {b},
          decrees  : {decrees},
          to       :
            {
              m.to :
                m \in
                  {
                    m \in msgs:
                      /\ m.type = BeginBallotMsgType
                      /\ m.ballotId = b
                  }
            }
        ]
      /\ UNCHANGED <<priestStatus, ledgers, usedBallotIds>>

\* Step (4)
ReceiveBeginBallotMsg(q) ==
  LET
    b == priestStatus[q].nextBallotId
    beginBallotMsgs ==
      {
        m \in msgs:
          /\ m.type = BeginBallotMsgType
          /\ m.ballotId = b
          /\ m.to = q
      }
  IN
    \E m \in beginBallotMsgs:
      /\ priestStatus' =
        [
          priestStatus EXCEPT ![q].prevVote =
            [
              i \in INSTANCE_IDS |->
                IF m.decrees[i] # BlankDecree
                  THEN [ballotId |-> b, decree |-> m.decrees[i]]
                  ELSE priestStatus[q].prevVote[i]
            ]
        ]
      /\ msgs' = msgs \union
        {[
          type     |-> VotedMsgType,
          ballotId |-> b,
          decrees  |-> m.decrees,
          from     |-> q
        ]}
      /\ UNCHANGED <<ledgers, minUnusedInstanceIds, usedBallotIds>>

\* Step (5)
ReceiveVotedMsg(p) ==
  \E i \in INSTANCE_IDS:
    LET
      b == priestStatus[p].lastTriedBallotId
      votedMsgs ==
        {
          m \in msgs:
            /\ m.type = VotedMsgType
            /\ m.ballotId = b
            /\ m.decrees[i] # BlankDecree
        }
      decrees ==
        IF votedMsgs # {}
          THEN (CHOOSE m \in votedMsgs: TRUE).decrees
          ELSE [j \in INSTANCE_IDS |-> BlankDecree]
    IN
      /\ GetQuorum(b, i) # {}
      /\ {m.from: m \in votedMsgs} = GetQuorum(b, i)
      /\ ledgers' = [ledgers EXCEPT ![p][i] = decrees[i]]
      /\ msgs' = msgs \union
        {[
          type     |-> SuccessMsgType,
          ballotId |-> b,
          decrees  |-> decrees
        ]}
      /\ UNCHANGED <<priestStatus, minUnusedInstanceIds, usedBallotIds>>

\* Step (6)
ReceiveSuccessMsg(q) ==
  \E successMsg \in {m \in msgs: m.type = SuccessMsgType}:
    /\ ledgers' =
      [
        ledgers EXCEPT ![q] =
          [
            i \in INSTANCE_IDS |->
              IF successMsg.decrees[i] # BlankDecree
                THEN successMsg.decrees[i]
                ELSE ledgers[q][i]
          ]
      ]
    /\ UNCHANGED <<priestStatus, minUnusedInstanceIds, usedBallotIds, msgs>>

Next == \E p \in PRIESTS:
  \/ SendNextBallotMsg(p)
  \/ ReceiveNextBallotMsg(p)
  \/ ReceiveLastVoteMsg(p)
  \/ SendBeginBallotMsg(p)
  \/ ReceiveBeginBallotMsg(p)
  \/ ReceiveVotedMsg(p)
  \/ ReceiveSuccessMsg(p)

Spec ==
  /\ Init
  /\ [][Next]_<<priestStatus, ledgers, minUnusedInstanceIds, usedBallotIds, msgs>>
  /\ SF_<<priestStatus, ledgers, minUnusedInstanceIds, usedBallotIds, msgs>>(Next)

ValidMinUnusedInstanceIds ==
         {InvalidInstanceId}
  \union 0..((CHOOSE mid \in INSTANCE_IDS: \A id \in INSTANCE_IDS: mid >= id) + 1)
ValidBallotIds == {BlankBallotId} \union BALLOT_IDS
ValidDecrees == {BlankDecree, OliveDayDecree} \union DECREES
PriestStatusTypeOK ==
  /\ DOMAIN priestStatus = PRIESTS
  /\ \A p \in PRIESTS:
    /\ DOMAIN priestStatus[p] =
      {"lastTriedBallotId", "prevVote", "nextBallotId"}
    /\ priestStatus[p].lastTriedBallotId \in ValidBallotIds
    /\ DOMAIN priestStatus[p].prevVote = INSTANCE_IDS
    /\ \A i \in INSTANCE_IDS:
      /\ DOMAIN priestStatus[p].prevVote[i] = {"ballotId", "decree"}
      /\ priestStatus[p].prevVote[i].ballotId \in ValidBallotIds
      /\ priestStatus[p].prevVote[i].decree \in ValidDecrees
    /\ priestStatus[p].nextBallotId \in ValidBallotIds
  /\ priestStatus \in
    [
      PRIESTS ->
        [
          lastTriedBallotId : ValidBallotIds,
          prevVote          :
            [
              INSTANCE_IDS ->
                [
                  ballotId  : ValidBallotIds,
                  decree    : ValidDecrees
                ]
            ],
          nextBallotId      : ValidBallotIds
        ]
    ]
LedgersTypeOK ==
  /\ DOMAIN ledgers = PRIESTS
  /\ \A p \in PRIESTS:
    /\ DOMAIN ledgers[p] = INSTANCE_IDS
    /\ \A i \in INSTANCE_IDS:
      /\ ledgers[p][i] \in ValidDecrees
  /\ ledgers \in [PRIESTS -> [INSTANCE_IDS -> ValidDecrees]]
MinUnusedInstanceIdsTypeOK ==
  /\ DOMAIN minUnusedInstanceIds = PRIESTS
  /\ \A p \in PRIESTS:
    /\ minUnusedInstanceIds[p] \in ValidMinUnusedInstanceIds
  /\ minUnusedInstanceIds \in [PRIESTS -> ValidMinUnusedInstanceIds]
UsedBallotIdsTypeOK == usedBallotIds \subseteq BALLOT_IDS
MsgsTypeOK ==
  /\ \A m \in msgs:
    \/ /\ m.type = NextBallotMsgType
       /\ m.ballotId \in BALLOT_IDS
    \/ /\ m.type = LastVoteMsgType
       /\ m.ballotId \in BALLOT_IDS
       /\ DOMAIN m.vote = INSTANCE_IDS
       /\ \A i \in INSTANCE_IDS:
         /\ DOMAIN m.vote[i] = {"ballotId", "decree"}
         /\ m.vote[i].ballotId \in ValidBallotIds
         /\ m.vote[i].decree \in ValidDecrees
       /\ m.from \in PRIESTS
    \/ /\ m.type = BeginBallotMsgType
       /\ m.ballotId \in BALLOT_IDS
       /\ DOMAIN m.decrees = INSTANCE_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
       /\ m.to \in PRIESTS
    \/ /\ m.type = VotedMsgType
       /\ m.ballotId \in BALLOT_IDS
       /\ DOMAIN m.decrees = INSTANCE_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
       /\ m.from \in PRIESTS
    \/ /\ m.type = SuccessMsgType
       /\ m.ballotId \in BALLOT_IDS
       /\ DOMAIN m.decrees = INSTANCE_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
  /\ msgs \subseteq
           [type : {NextBallotMsgType}, ballotId : BALLOT_IDS]
    \union [type     : {LastVoteMsgType},
            ballotId : BALLOT_IDS,
            vote     : [INSTANCE_IDS ->
                         [ballotId : ValidBallotIds, decree : ValidDecrees]],
            from     : PRIESTS]
    \union [type     : {BeginBallotMsgType},
            ballotId : BALLOT_IDS,
            decrees  : [INSTANCE_IDS -> ValidDecrees],
            to       : PRIESTS]
    \union [type     : {VotedMsgType},
            ballotId : BALLOT_IDS,
            decrees  : [INSTANCE_IDS -> ValidDecrees],
            from     : PRIESTS]
    \union [type     : {SuccessMsgType},
            ballotId : BALLOT_IDS,
            decrees  : [INSTANCE_IDS -> ValidDecrees]]
TypeOK ==
  /\ PriestStatusTypeOK
  /\ LedgersTypeOK
  /\ MinUnusedInstanceIdsTypeOK
  /\ UsedBallotIdsTypeOK
  /\ MsgsTypeOK

B1Consistent ==
  /\ \A p1, p2 \in {p \in PRIESTS: priestStatus[p].lastTriedBallotId # BlankBallotId}:
    \/ p1 = p2
    \/ priestStatus[p1].lastTriedBallotId # priestStatus[p2].lastTriedBallotId
  /\ \A m1, m2 \in {m \in msgs: m.type = BeginBallotMsgType}:
    \/ \A i \in INSTANCE_IDS:
      \/ m1.decrees[i] = BlankDecree
      \/ m2.decrees[i] = BlankDecree
      \/ m1.decrees[i] = m2.decrees[i]
    \/ m1.ballotId # m2.ballotId

B2Consistent ==
  \A i \in INSTANCE_IDS:
    \A m1, m2 \in
      {m \in msgs: m.type = BeginBallotMsgType /\ m.decrees[i] # BlankDecree}:
        GetQuorum(m1.ballotId, i) \intersect GetQuorum(m2.ballotId, i) # {}

B3Consistent ==
  \A beginBallotMsg \in {m \in msgs: m.type = BeginBallotMsgType}:
    \A i \in INSTANCE_IDS:
      LET
        quorum == GetQuorum(beginBallotMsg.ballotId, i)
        votedMsgs ==
          {
            m \in msgs:
              /\ m.type = VotedMsgType
              /\ m.ballotId < beginBallotMsg.ballotId
              /\ m.decrees[i] # BlankDecree
              /\ m.from \in quorum
          }
        latestEarlierBallotId ==
          IF votedMsgs # {}
            THEN
              (CHOOSE latestMsg \in votedMsgs:
                \A m \in votedMsgs:
                  latestMsg.ballotId >= m.ballotId).ballotId
            ELSE BlankBallotId
        latestEarlierDecree ==
          IF latestEarlierBallotId # BlankBallotId
            THEN (CHOOSE m \in votedMsgs:
              m.ballotId = latestEarlierBallotId).decrees[i]
            ELSE BlankDecree
      IN
        \/ beginBallotMsg.decrees[i] = BlankDecree
        \/ latestEarlierDecree = BlankDecree
        \/ beginBallotMsg.decrees[i] = latestEarlierDecree

LemmaConsistent ==
  \A m1 \in {m \in msgs: m.type = SuccessMsgType}:
    \A m2 \in {m \in msgs: m.type = BeginBallotMsgType /\ m.ballotId > m1.ballotId}:
      \A i \in INSTANCE_IDS:
        \/ m1.decrees[i] = BlankDecree
        \/ m2.decrees[i] = BlankDecree
        \/ m2.decrees[i] = m1.decrees[i]

Theorem1Consistent ==
  \A m1, m2 \in {m \in msgs: m.type = SuccessMsgType}:
    \A i \in INSTANCE_IDS:
      \/ m1.decrees[i] = BlankDecree
      \/ m2.decrees[i] = BlankDecree
      \/ m1.decrees[i] = m2.decrees[i]

LedgerConsistent ==
  \A p1, p2 \in PRIESTS:
    \A i \in INSTANCE_IDS:
      \/ ledgers[p1][i] = BlankDecree
      \/ ledgers[p2][i] = BlankDecree
      \/ ledgers[p1][i] = ledgers[p2][i]

Consistent ==
  /\ B1Consistent
  /\ B2Consistent
  /\ B3Consistent
  /\ LemmaConsistent
  /\ Theorem1Consistent
  /\ LedgerConsistent

Invariant ==
  /\ TypeOK
  /\ Consistent

\* If decrees A and B are important and
\* decree A was passed before decree B was proposed,
\* then A has a lower decree number than B.
DecreeOrderingProperty ==
  [][
    LET
      GetInstanceIds(messages, messageType, excludedDecrees) ==
        {
          i \in INSTANCE_IDS:
            \E m \in messages:
              /\ m.type = messageType
              /\ m.decrees[i] \notin excludedDecrees
        }
      instanceIdsOfSuccessMsgs ==
        GetInstanceIds(msgs, SuccessMsgType, {BlankDecree})
      importantInstanceIdsOfSuccessMsgs ==
        GetInstanceIds(msgs, SuccessMsgType, {BlankDecree, OliveDayDecree})
      importantInstanceIdsOfBeginBallotMsgs ==
          GetInstanceIds(msgs', BeginBallotMsgType, {BlankDecree, OliveDayDecree})
        \ GetInstanceIds(msgs, BeginBallotMsgType, {BlankDecree, OliveDayDecree})
    IN
      \A instanceIdOfSuccessMsg \in importantInstanceIdsOfSuccessMsgs:
        \A instanceIdOfBeginBallotMsg \in importantInstanceIdsOfBeginBallotMsgs:
          instanceIdOfBeginBallotMsg > instanceIdOfSuccessMsg
  ]_<<
    priestStatus,
    ledgers,
    minUnusedInstanceIds,
    usedBallotIds,
    msgs>>

LivenessProperty ==
  <>(ledgers \in [PRIESTS -> [INSTANCE_IDS -> {OliveDayDecree} \union DECREES]])

Property ==
  /\ DecreeOrderingProperty
  /\ LivenessProperty
============================================================================
```

```cfg
\* MultiDecreeParliament.cfg
CONSTANT
PRIESTS = {p1, p2, p3}
DECREES = {d1, d2}
INSTANCE_IDS = {0, 1}
BALLOT_IDS = {0, 1}

SPECIFICATION
Spec

INVARIANT
Invariant

PROPERTY
Property
```

```bash
java -Xms120g -XX:+UseParallelGC -XX:MaxDirectMemorySize=120g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -cp /usr/local/lib/tla2tools.jar tlc2.TLC MultiDecreeParliament -workers auto -checkpoint 0
# TLC2 Version 2.18 of Day Month 20?? (rev: 5b3286b)
# Running breadth-first search Model-Checking with fp 2 and seed 183920139505302825 with 128 workers on 128 cores with 117760MB heap and 122880MB offheap memory [pid: 3237] (Linux 3.10.0-1160.90.1.el7.x86_64 amd64, Red Hat, Inc. 11.0.19 x86_64, OffHeapDiskFPSet, DiskStateQueue).
# ...
# Starting... (2023-07-23 23:20:11)
# Implied-temporal checking--satisfiability problem has 1 branches.
# ...
# Checking temporal properties for the current state space with 61839191 total distinct states at (2023-07-24 01:43:52)
# Finished checking temporal properties in 16min 08s at 2023-07-24 02:00:01
# ...
# Checking temporal properties for the complete state space with 65659825 total distinct states at (2023-07-24 02:12:19)
# Finished checking temporal properties in 18min 19s at 2023-07-24 02:30:38
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = .0025
#   based on the actual fingerprints:  val = .0019
# 763561969 states generated, 65659825 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 33.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 13 and the 95th percentile is 3).
# Finished in 03h 10min at (2023-07-24 02:30:44)
```

# Reference

+ [The Beginner's Guide to TLA+: Specifying and Verifying Distributed Systems](https://clcanny.github.io/2023/06/26/computer-science/programming-language/tla+/the-beginner-s-guide-to-tla+-specifying-and-verifying-distributed-systems/)
+ [tlaplus/tlaplus: When checking liveness, TLC can stall with 0s/min when behavior graph gets huge](https://github.com/tlaplus/tlaplus/issues/636)
+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
