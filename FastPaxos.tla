--------------------------- MODULE FastPaxos -------------------------------
\* FastPaxos.tla
EXTENDS Integers, FiniteSets, TLC
CONSTANTS COORS,
          ACCS,
          \* Any set of at least $N - F$ acceptors is a classic quorum.
          F,
          \* Any set of at least $N - E$ acceptors is a fast quorum.
          E,
          VALS,
          INST_IDS,
          RND_IDS
VARIABLES \* The highest-numbered round that coordinator $c$ has begun.
          crnd,
          \* The highest-numbered round in which acceptor $a$ has participated.
          rnd,
          \* The highest-numbered round in which acceptor $a$ has cast a vote.
          vrnd,
          \* The value acceptor $a$ voted to accept in
          \* round $\operatorname{vrnd}(a)$.
          vval,
          minUnusedInstanceIds,
          usedRoundIds,
          msgs

BnkVal == "BLANK"
AnyVal == "ANY"
OliveDayVal == "The ides of February is national olive day"
InvInstId == -1
BnkRnd == -1

P1AMT == "phase-1a"
P1BMT == "phase-1b"
P2AMT == "phase-2a"
P2BMT == "phase-2b"

ASSUME
  /\ IsFiniteSet(COORS)
  /\ IsFiniteSet(ACCS)
  /\ Cardinality(ACCS) > 2 * F
  /\ Cardinality(ACCS) > 2 * E + F
  /\ F >= E
  /\ IsFiniteSet(VALS)
  /\ BnkVal \notin VALS
  /\ AnyVal \notin VALS
  /\ OliveDayVal \notin VALS
  /\ INST_IDS \subseteq Nat
  /\ IsFiniteSet(INST_IDS)
  /\ \A i \in INST_IDS: InvInstId < i
  /\ RND_IDS \subseteq Nat
  /\ IsFiniteSet(RND_IDS)
  /\ BnkRnd \notin RND_IDS

Max(s) == CHOOSE m \in s: \forall n \in s: m >= n

Init ==
  /\ crnd = [c \in COORS |-> BnkRnd]
  /\ rnd = [a \in ACCS |-> BnkRnd]
  /\ vrnd = [a \in ACCS |-> [i \in INST_IDS |-> BnkRnd]]
  /\ vval = [a \in ACCS |-> [i \in INST_IDS |-> BnkVal]]
  /\ minUnusedInstanceIds = [c \in COORS |-> InvInstId]
  /\ usedRoundIds = {}
  /\ msgs = {}

Phase1A(c) ==
  \E r \in RND_IDS \ usedRoundIds:
    /\ r > crnd[c]
    /\ crnd' = [crnd EXCEPT ![c] = r]
    /\ usedRoundIds' = usedRoundIds \union {r}
    /\ msgs' = msgs \union {[type |-> P1AMT, rnd |-> b]}
    /\ UNCHANGED <<rnd, vrnd, vval, minUnusedInstanceIds>>

Phase1B(a) ==
  \E r \in RND_IDS:
    /\ [type |-> P1AMT, rnd |-> r] \in msgs
    /\ r > rnd[a]
    /\ rnd' = [rnd EXCEPT ![a] = r]
    /\ msgs' = msgs \union {[
        type     |-> P1BMT,
        rnd  |-> r,
        vr       |-> vrnd[a],
        vv       |-> vval[a],
        from     |-> a
      ]}
    /\ UNCHANGED <<crnd, vrnd, vval, minUnusedInstanceIds, usedRoundIds>>


ChsPhs1BMsgs(accs, r) ==
  {
    m \in msgs:
      /\ m.type = Phs1BMT
      /\ m.rnd = r
      /\ m.from \in accs
  }
ChsVSatO4(q, i, r) ==
  LET
    msgs = ChsPhs1BMsgs(q, i, r)
    \* Let $k$ be the largest value of $\operatorname{vr}(a)$ for all $a$ in $Q$.
    k == Max({m.vr[i]: m \in msgs})
ChsVsSatO4(accs, r) ==
  LET
    k ==
    v ==
    vs ==
    ChsVSatO4(accs, i, r) ==
      LET vvs == {m.vv[i]: m \in ChsPhs1BMsgs(accs) /\ m.rnd = r}
      IN IF Cardinality(vvs) == 1 THEN vvs ELSE {}
  IN
    [i \in INST_IDS |-> ChsVSatO4(accs, i, r)]
Phase2A(c) ==
  \E q \in {q \in SUBSET ACCS: Cardinality(q) >= N - F}:
    LET
      rqs == {rq \in SUBSET q: Cardinality(rq) >= (N - F) + (N - E) - N}
      phs1BMsgs == ChsPhs1BMsgs(q, rnd[c])
      maxVrs == [i \in INST_IDS |-> Max({m \in phs1BMsgs: m.vr[i]})]
      vvsSatO4 == [i \in INST_IDS: {m \in phs1BMsgs: m.from \in rqs
      notBlankInstIds == {i \in INST_IDS: maxVrs[i] # BnkRnd}
      maxNotBlankInstId ==
        IF notBlankInstIds = {}
          THEN InvInstId
          ELSE
            CHOOSE mid \in notBlankInstIds:
              \A id \in notBlankInstIds: mid >= id
      values ==
        [
          i \in INST_IDS |->
            IF i > maxNotBlankInstId
              THEN BnkVal
              ELSE
                IF maxVrs[i].rnd = BnkRnd
                  THEN OliveDayVal
                  ELSE maxLastVotes[i].decree
        ]
    IN
      /\ {m \in msgs: m.type = P2AMT /\ m.rnd = b} = {}
      /\ {m.from: m \in phase1BMsgs} = quorum
      /\ Cardinality(quorum) * 2 > Cardinality(PRIESTS)
      /\ minUnusedInstanceIds' =
        [minUnusedInstanceIds EXCEPT ![p] = maxNotBlankInstId + 1]
      /\ msgs' = msgs \union
        [
          type     : {P2AMT},
          rnd : {b},
          decrees  : {decrees},
          to       : quorum
        ]
      /\ UNCHANGED <<priestStatus, ledgers, usedRoundIds>>

\* Step (3.2)
\* Then, whenever he receives a request to pass a decree,
\* he chooses the lowest-numbered decree that he is still free to choose,
\* and he performs step 3 for that decree number
\* (instance of the Synod protocol) to try to pass the decree.
SendBeginBallotMsg(p) ==
  \E d \in DECREES:
    LET
      b == priestStatus[p].lastTriedBallotId
      instanceIds == {i \in INST_IDS: i >= minUnusedInstanceIds[p]}
      instanceId ==
        IF instanceIds # {}
          THEN CHOOSE mid \in instanceIds: \A id \in instanceIds: mid <= id
          ELSE InvInstId
      decrees ==
        [i \in INST_IDS |-> IF i = instanceId THEN d ELSE BnkVal]
    IN
      \* Ensure that Step (3.1) has been successfully completed
      \* before proceeding further.
      /\ minUnusedInstanceIds[p] # InvInstId
      \* Ensure that available instance IDs remain.
      /\ instanceId # InvInstId
      /\ minUnusedInstanceIds' =
        [minUnusedInstanceIds EXCEPT ![p] = instanceId + 1]
      /\ msgs' = msgs \union
        [
          type     : {P2AMT},
          rnd : {b},
          decrees  : {decrees},
          to       :
            {
              m.to :
                m \in
                  {
                    m \in msgs:
                      /\ m.type = P2AMT
                      /\ m.rnd = b
                  }
            }
        ]
      /\ UNCHANGED <<priestStatus, ledgers, usedRoundIds>>

\* Step (4)
ReceiveBeginBallotMsg(q) ==
  LET
    b == priestStatus[q].nextBallotId
    beginBallotMsgs ==
      {
        m \in msgs:
          /\ m.type = P2AMT
          /\ m.rnd = b
          /\ m.to = q
      }
  IN
    \E m \in beginBallotMsgs:
      /\ priestStatus' =
        [
          priestStatus EXCEPT ![q].prevVote =
            [
              i \in INST_IDS |->
                IF m.decrees[i] # BnkVal
                  THEN [rnd |-> b, decree |-> m.decrees[i]]
                  ELSE priestStatus[q].prevVote[i]
            ]
        ]
      /\ msgs' = msgs \union
        {[
          type     |-> P2BMT,
          rnd |-> b,
          decrees  |-> m.decrees,
          from     |-> q
        ]}
      /\ UNCHANGED <<ledgers, minUnusedInstanceIds, usedRoundIds>>

\* Step (5)
ReceiveVotedMsg(p) ==
  \E i \in INST_IDS:
    LET
      b == priestStatus[p].lastTriedBallotId
      votedMsgs ==
        {
          m \in msgs:
            /\ m.type = P2BMT
            /\ m.rnd = b
            /\ m.decrees[i] # BnkVal
        }
      decrees ==
        IF votedMsgs # {}
          THEN (CHOOSE m \in votedMsgs: TRUE).decrees
          ELSE [j \in INST_IDS |-> BnkVal]
    IN
      /\ GetQuorum(b, i) # {}
      /\ {m.from: m \in votedMsgs} = GetQuorum(b, i)
      /\ ledgers' = [ledgers EXCEPT ![p][i] = decrees[i]]
      /\ msgs' = msgs \union
        {[
          type     |-> SuccessMsgType,
          rnd |-> b,
          decrees  |-> decrees
        ]}
      /\ UNCHANGED <<priestStatus, minUnusedInstanceIds, usedRoundIds>>

\* Step (6)
ReceiveSuccessMsg(q) ==
  \E successMsg \in {m \in msgs: m.type = SuccessMsgType}:
    /\ ledgers' =
      [
        ledgers EXCEPT ![q] =
          [
            i \in INST_IDS |->
              IF successMsg.decrees[i] # BnkVal
                THEN successMsg.decrees[i]
                ELSE ledgers[q][i]
          ]
      ]
    /\ UNCHANGED <<priestStatus, minUnusedInstanceIds, usedRoundIds, msgs>>

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
  /\ [][Next]_<<priestStatus, ledgers, minUnusedInstanceIds, usedRoundIds, msgs>>
  /\ SF_<<priestStatus, ledgers, minUnusedInstanceIds, usedRoundIds, msgs>>(Next)

ValidMinUnusedInstanceIds ==
         {InvInstId}
  \union 0..((CHOOSE mid \in INST_IDS: \A id \in INST_IDS: mid >= id) + 1)
ValidBallotIds == {BnkRnd} \union RND_IDS
ValidDecrees == {BnkVal, OliveDayVal} \union DECREES
PriestStatusTypeOK ==
  /\ DOMAIN priestStatus = PRIESTS
  /\ \A p \in PRIESTS:
    /\ DOMAIN priestStatus[p] =
      {"lastTriedBallotId", "prevVote", "nextBallotId"}
    /\ priestStatus[p].lastTriedBallotId \in ValidBallotIds
    /\ DOMAIN priestStatus[p].prevVote = INST_IDS
    /\ \A i \in INST_IDS:
      /\ DOMAIN priestStatus[p].prevVote[i] = {"rnd", "decree"}
      /\ priestStatus[p].prevVote[i].rnd \in ValidBallotIds
      /\ priestStatus[p].prevVote[i].decree \in ValidDecrees
    /\ priestStatus[p].nextBallotId \in ValidBallotIds
  /\ priestStatus \in
    [
      PRIESTS ->
        [
          lastTriedBallotId : ValidBallotIds,
          prevVote          :
            [
              INST_IDS ->
                [
                  rnd  : ValidBallotIds,
                  decree    : ValidDecrees
                ]
            ],
          nextBallotId      : ValidBallotIds
        ]
    ]
LedgersTypeOK ==
  /\ DOMAIN ledgers = PRIESTS
  /\ \A p \in PRIESTS:
    /\ DOMAIN ledgers[p] = INST_IDS
    /\ \A i \in INST_IDS:
      /\ ledgers[p][i] \in ValidDecrees
  /\ ledgers \in [PRIESTS -> [INST_IDS -> ValidDecrees]]
MinUnusedInstanceIdsTypeOK ==
  /\ DOMAIN minUnusedInstanceIds = PRIESTS
  /\ \A p \in PRIESTS:
    /\ minUnusedInstanceIds[p] \in ValidMinUnusedInstanceIds
  /\ minUnusedInstanceIds \in [PRIESTS -> ValidMinUnusedInstanceIds]
UsedBallotIdsTypeOK == usedRoundIds \subseteq RND_IDS
MsgsTypeOK ==
  /\ \A m \in msgs:
    \/ /\ m.type = P1AMT
       /\ m.rnd \in RND_IDS
    \/ /\ m.type = P1BMT
       /\ m.rnd \in RND_IDS
       /\ DOMAIN m.vote = INST_IDS
       /\ \A i \in INST_IDS:
         /\ DOMAIN m.vote[i] = {"rnd", "decree"}
         /\ m.vote[i].rnd \in ValidBallotIds
         /\ m.vote[i].decree \in ValidDecrees
       /\ m.from \in PRIESTS
    \/ /\ m.type = P2AMT
       /\ m.rnd \in RND_IDS
       /\ DOMAIN m.decrees = INST_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
       /\ m.to \in PRIESTS
    \/ /\ m.type = P2BMT
       /\ m.rnd \in RND_IDS
       /\ DOMAIN m.decrees = INST_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
       /\ m.from \in PRIESTS
    \/ /\ m.type = SuccessMsgType
       /\ m.rnd \in RND_IDS
       /\ DOMAIN m.decrees = INST_IDS
       /\ \A i \in DOMAIN m.decrees: m.decrees[i] \in ValidDecrees
  /\ msgs \subseteq
           [type : {P1AMT}, rnd : RND_IDS]
    \union [type     : {P1BMT},
            rnd : RND_IDS,
            vote     : [INST_IDS ->
                         [rnd : ValidBallotIds, decree : ValidDecrees]],
            from     : PRIESTS]
    \union [type     : {P2AMT},
            rnd : RND_IDS,
            decrees  : [INST_IDS -> ValidDecrees],
            to       : PRIESTS]
    \union [type     : {P2BMT},
            rnd : RND_IDS,
            decrees  : [INST_IDS -> ValidDecrees],
            from     : PRIESTS]
    \union [type     : {SuccessMsgType},
            rnd : RND_IDS,
            decrees  : [INST_IDS -> ValidDecrees]]
TypeOK ==
  /\ PriestStatusTypeOK
  /\ LedgersTypeOK
  /\ MinUnusedInstanceIdsTypeOK
  /\ UsedBallotIdsTypeOK
  /\ MsgsTypeOK

B1Consistent ==
  /\ \A p1, p2 \in {p \in PRIESTS: priestStatus[p].lastTriedBallotId # BnkRnd}:
    \/ p1 = p2
    \/ priestStatus[p1].lastTriedBallotId # priestStatus[p2].lastTriedBallotId
  /\ \A m1, m2 \in {m \in msgs: m.type = P2AMT}:
    \/ \A i \in INST_IDS:
      \/ m1.decrees[i] = BnkVal
      \/ m2.decrees[i] = BnkVal
      \/ m1.decrees[i] = m2.decrees[i]
    \/ m1.rnd # m2.rnd

B2Consistent ==
  \A i \in INST_IDS:
    \A m1, m2 \in
      {m \in msgs: m.type = P2AMT /\ m.decrees[i] # BnkVal}:
        GetQuorum(m1.rnd, i) \intersect GetQuorum(m2.rnd, i) # {}

B3Consistent ==
  \A beginBallotMsg \in {m \in msgs: m.type = P2AMT}:
    \A i \in INST_IDS:
      LET
        quorum == GetQuorum(beginBallotMsg.rnd, i)
        votedMsgs ==
          {
            m \in msgs:
              /\ m.type = P2BMT
              /\ m.rnd < beginBallotMsg.rnd
              /\ m.decrees[i] # BnkVal
              /\ m.from \in quorum
          }
        latestEarlierBallotId ==
          IF votedMsgs # {}
            THEN
              (CHOOSE latestMsg \in votedMsgs:
                \A m \in votedMsgs:
                  latestMsg.rnd >= m.rnd).rnd
            ELSE BnkRnd
        latestEarlierDecree ==
          IF latestEarlierBallotId # BnkRnd
            THEN (CHOOSE m \in votedMsgs:
              m.rnd = latestEarlierBallotId).decrees[i]
            ELSE BnkVal
      IN
        \/ beginBallotMsg.decrees[i] = BnkVal
        \/ latestEarlierDecree = BnkVal
        \/ beginBallotMsg.decrees[i] = latestEarlierDecree

LemmaConsistent ==
  \A m1 \in {m \in msgs: m.type = SuccessMsgType}:
    \A m2 \in {m \in msgs: m.type = P2AMT /\ m.rnd > m1.rnd}:
      \A i \in INST_IDS:
        \/ m1.decrees[i] = BnkVal
        \/ m2.decrees[i] = BnkVal
        \/ m2.decrees[i] = m1.decrees[i]

Theorem1Consistent ==
  \A m1, m2 \in {m \in msgs: m.type = SuccessMsgType}:
    \A i \in INST_IDS:
      \/ m1.decrees[i] = BnkVal
      \/ m2.decrees[i] = BnkVal
      \/ m1.decrees[i] = m2.decrees[i]

LedgerConsistent ==
  \A p1, p2 \in PRIESTS:
    \A i \in INST_IDS:
      \/ ledgers[p1][i] = BnkVal
      \/ ledgers[p2][i] = BnkVal
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
          i \in INST_IDS:
            \E m \in messages:
              /\ m.type = messageType
              /\ m.decrees[i] \notin excludedDecrees
        }
      instanceIdsOfSuccessMsgs ==
        GetInstanceIds(msgs, SuccessMsgType, {BnkVal})
      importantInstanceIdsOfSuccessMsgs ==
        GetInstanceIds(msgs, SuccessMsgType, {BnkVal, OliveDayVal})
      importantInstanceIdsOfBeginBallotMsgs ==
          GetInstanceIds(msgs', P2AMT, {BnkVal, OliveDayVal})
        \ GetInstanceIds(msgs, P2AMT, {BnkVal, OliveDayVal})
    IN
      \A instanceIdOfSuccessMsg \in importantInstanceIdsOfSuccessMsgs:
        \A instanceIdOfBeginBallotMsg \in importantInstanceIdsOfBeginBallotMsgs:
          instanceIdOfBeginBallotMsg > instanceIdOfSuccessMsg
  ]_<<
    priestStatus,
    ledgers,
    minUnusedInstanceIds,
    usedRoundIds,
    msgs>>

LivenessProperty ==
  <>(ledgers \in [PRIESTS -> [INST_IDS -> {OliveDayVal} \union DECREES]])

Property ==
  /\ DecreeOrderingProperty
  /\ LivenessProperty
============================================================================
