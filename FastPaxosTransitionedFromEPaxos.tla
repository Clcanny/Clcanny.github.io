\* FastPaxosTransitionedFromEPaxos.tla
------------------- MODULE FastPaxosTransitionedFromEPaxos ------------------
EXTENDS Naturals, FiniteSets

Max(S) == CHOOSE i \in S : \A j \in S : j \leq i

CONSTANTS Val,             \* The set of values that may be proposed.
          Delta,           \* The set of values that each acceptor decided
                           \* on itself.
          None,            \*
          Rep,             \* The set of replicas.
                           \* Rep = Coordinator
                           \*     + Acc
                           \*     + Proposer
                           \*     + Learner
          FastQuorum,      \* The set of fast quorums.
          SlowQuorum,      \* The set of slow quorums.
          CoordOf(_),      \* The coordinator of round $i$.
          NotSeen,         \* Status.
          PreAccepted,     \*
          Accepted,        \*
          Committed,       \*
          PreAccept,       \* Message.
          PreAcceptOK,     \*
          Accept,          \*
          AcceptOK,        \*
          Prepare,         \*
          PrepareOK        \*

ASSUME None \notin (Val \cup Delta)

ASSUME IsFiniteSet(Rep)
\* In EPaxos, each replica serves dual roles: an acceptor and a coordinator.
Acc   == Rep    \* the set of acceptors.
Coord == Rep    \* the set of coordinators.

ASSUME /\ FastQuorum \subseteq SUBSET Acc
       /\ SlowQuorum \subseteq SUBSET Acc
       /\ \A Q, R \in (SlowQuorum \cup FastQuorum) : Q \cap R # {}
       /\ \A Q \in SlowQuorum :
            \A R1, R2 \in FastQuorum :
              Q \cap R1 \cap R2 # {}

RNum       == Nat \ {0}
FastNum    == CHOOSE n \in RNum : \A i \in RNum : n <= i
ClassicNum == RNum \ {FastNum}
ASSUME /\ \A i \in RNum : CoordOf(i) \in Coord

Status == {NotSeen, PreAccepted, Accepted, Committed}
ASSUME Cardinality(Status) = 4

CmdLog == [rnd : Nat, status : Status, val : Val, delta : Delta]

Message ==
  \* Establish ordering constraints.
       [type : {PreAccept},   rnd : RNum, val : Val, delta : Delta]
  \cup [type : {PreAcceptOK}, rnd : RNum, val : Val, delta : Delta, acc : Acc]
  \* Paxos-Accept.
  \cup [type : {Accept},      rnd : RNum, val : Val, delta : Delta]
  \cup [type : {AcceptOK},    rnd : RNum, val : Val, delta : Delta, acc : Acc]
  \* Explicit Prepare.
  \cup [type : {Prepare},     rnd : RNum]
  \cup [type : {PrepareOK},   rnd : RNum, cmdLog : CmdLog, acc : Acc]
ASSUME Cardinality({m.type : m \in Message}) == 6
-----------------------------------------------------------------------------

VARIABLES cmdLog,      \* In EPaxos, the $cmdLog$ variable is employed as
                       \* a replacement for
                       \* $rnd$, $vrnd$, $vval$, $crnd$, and $cval$
                       \* from Fast Paxos.
          amLeader,    \* The leader-selection algorithm
                       \* is represented by a variable $amLeader$,
                       \* where $amLeader[c]$ is a Boolean that is true
                       \* iff coordinator $c$ believes itself
                       \* to be the current leader.
          sentMsg,
          proposed,    \* For simplicity, the specification does not
                       \* describe proposers.
                       \* Instead, it contains a variable $proposed$
                       \* whose value represents the set of
                       \* proposed values.
          learned,     \* For simplicity, the specification does not
                       \* describe learners.
                       \* Instead, it contains a variable $learned$
                       \* whose value represents the set of
                       \* learned values.
          goodSet

oVars == <<amLeader, proposed, learned, goodSet>>  \* Most other variables.
vars  == <<cmdLog, oVars, sentMsg>>                \* All variables.
-----------------------------------------------------------------------------

TypeOK ==
  /\ cmdLog \in [Rep -> CmdLog]
  /\ amLeader \in [Coord -> BOOLEAN]
  /\ sentMsg  \in SUBSET Message
  /\ proposed \in SUBSET Val
  /\ learned  \in SUBSET Val
  /\ goodSet \subseteq Rep

Init ==
  /\ cmdLog = [r \in Rep |-> rnd : 0, status : NotSeen, val : none, delta: none]
  /\ amLeader \in [Coord -> BOOLEAN]
  /\ sentMsg  = {}
  /\ proposed = {}
  /\ learned  = {}
  /\ goodSet \in SUBSET Rep
-----------------------------------------------------------------------------

Send(m) == sentMsg' = sentMsg \cup {m}
-----------------------------------------------------------------------------

EstablishOrderingConstraintsA(c, i, v, d) ==
  /\ amLeader[c]
  /\ c = CoordOf(i)
  /\ i = FastNum
  /\ cmdLog[c].rnd = 0
  /\ cmdLog[c].status = NotSeen
  /\ cmdLog' = [cmdLog EXCEPT ![c].rnd = i,
                              ![c].status = PreAccepted,
                              ![c].val = v,
                              ![c].delta = d]
  /\ Send([type |-> PreAccept, rnd |-> i, value |-> v, delta |-> d])
  /\ UNCHANGED <<oVars>>

Phase1a(c, i) ==
  /\ amLeader[c]
  /\ c = CoordOf(i)
  (*************************************************************************)
  (*`^The explicit prepare process is initiated by another replica,        *)
  (* denoted as $Q$, only when there is suspicion that                     *)
  (* the designated leader, labelled as $L$, has potentially failed.^'     *)
  (*************************************************************************)
  /\ c # CoordOf(FastNum)
  /\ cmdLog[c].rnd < i
  (*************************************************************************)
  (*`^CA2. A coordinator $c$ performs an action only if                    *)
  (* it believes itself to be the current leader.                          *)
  (* It begins a new round $i$ only if either $crnd[c] = 0$ or             *)
  (* it has learned that a round $j$ has been started,                     *)
  (* for some j with $crnd[c] < j < i$.^'                                  *)
  (*************************************************************************)
  /\ \/ /\ cmdLog[c].rnd = 0
        /\ cmdLog[c].status = NotSeen
        /\ cmdLog[c].majval = none
        /\ cmdLog[c].minval = none
     \/ \E m \in sentMsg : /\ crnd[c] < m.rnd
                           /\ m.rnd < i
     \/ /\ crnd[c] \in FastNum
        /\ i \in ClassicNum
  /\ cmd =
  /\ crnd' = [crnd EXCEPT ![c] = i]
  /\ cval' = [cval EXCEPT ![c] = none]
  /\ Send([type |-> "phase1a", rnd |-> i])
  /\ UNCHANGED <<aVars, oVars>>

(***************************************************************************)
(*`^$MsgsFrom(Q, i, phase)$ is defined to be the set of messages in        *)
(* $sentMsg$ of type $phase$ (which may equal $"phase1b"$ or $"phase2b"$)  *)
(* sent in round $i$ by the acceptors in the set $Q$.^'                    *)
(***************************************************************************)
MsgsFrom(Q, i, phase) ==
   {m \in sentMsg : (m.type = phase) /\ (m.acc \in Q) /\ (m.rnd = i)}

(***************************************************************************)
(*`^If $M$ is the set of round $i$ phase 1b messages sent by the acceptors *)
(* in a quorum $Q$, then $IsPickableVal(Q, i, M, v)$ is true iff the rule  *)
(* of Fast Paxos, Figure 2 (page 20) allows the coordinator to send        *)
(* the value $v$ in a phase 2a message for round $i$.                      *)
(***************************************************************************)
IsPickableVal(Q, i, M, v) ==
  LET vr(a) == (CHOOSE m \in M : m.acc = a).vrnd
      vv(a) == (CHOOSE m \in M : m.acc = a).vval
      k == Max({vr(a) : a \in Q})
      V == {vv(a) : a \in {b \in Q : vr(b) = k}}
      O4(w) == \E R \in Quorum(k) :
                \A a \in R \cap Q : (vr(a) = k) /\ (vv(a) = w)
  IN  IF k = 0 THEN \/ v \in proposed
                    \/ /\ i \in FastNum
                       /\ v = any
               ELSE IF Cardinality(V) = 1
                      THEN v \in V
                      ELSE IF \E w \in V : O4(w)
                              THEN v = CHOOSE w \in V : O4(w)
                              ELSE v \in proposed

(***************************************************************************)
(*`^Action $Phase2a(c,v)$ specifies the execution of phase 2a by           *)
(* coordinator $c$ with value $v$, as described in Section 2.2.1           *)
(* (on page 5) and Section 2.2.2 (page 6),                                 *)
(* and refined by CA2' (Section 3.3, page 22).^'                           *)
(***************************************************************************)
Phase2a(c, v) ==
  LET i == crnd[c]
  IN  /\ i # 0
      /\ cval[c] = none
      /\ amLeader[c]
      /\ \E Q \in Quorum(i) :
          /\ \A r \in Q : \E m \in MsgsFrom(Q, i, "phase1b") : m.acc = r
          /\ IsPickableVal(Q, i, MsgsFrom(Q, i, "phase1b"), v)
      /\ cval' = [cval EXCEPT ![c] = v]
      /\ Send([type |-> "phase2a", rnd |-> i, val |-> v])
      /\ UNCHANGED <<crnd, aVars, oVars>>

(***************************************************************************)
(*`^$coordLastMsg(c)$ is defined to be the last message that coordinator   *)
(* $c$ sent, if $crnd[c]>0$.^'                                             *)
(***************************************************************************)
coordLastMsg(c) ==
 IF cval[c] = none
   THEN [type |-> "phase1a", rnd |-> crnd[c]]
   ELSE [type |-> "phase2a", rnd |-> crnd[c], val |-> cval[c]]

(***************************************************************************)
(*`^In action $CoordRetransmit(c)$, coordinator $c$ retransmits the last   *)
(* message it sent.  This action is a stuttering action (meaning it does   *)
(* not change the value of any variable, so it is a no-op) if that message *)
(* is still in $sentMsg$.  However, this action is needed because $c$      *)
(* might have failed after first sending the message and subsequently have *)
(* been repaired after the message was removed from $sentMsg$.^'           *)
(***************************************************************************)
CoordRetransmit(c) ==
  /\ amLeader[c]
  /\ crnd[c] # 0
  /\ Send(coordLastMsg(c))
  /\ UNCHANGED <<aVars, cVars, oVars>>

(***************************************************************************)
(*`^$CoordNext(c)$ is the next-state action of coordinator $c$---that is,  *)
(* the disjunct of the algorithm's complete next-state action that         *)
(* represents actions of that coordinator.^'                               *)
(***************************************************************************)
CoordNext(c) ==
  \/ \E i \in RNum : Phase1a(c, i)
  \/ \E v \in Val \cup {any} : Phase2a(c, v)
  \/ CoordRetransmit(c)
-----------------------------------------------------------------------------

EstablishOrderingConstraintsB(a, i) ==

(***************************************************************************)
(*`^Action $Phase1b(i, a)$ specifies the execution of phase 1b for round   *)
(* $i$ by acceptor $a$, described in Section 2.2.1 on page 5.^'            *)
(***************************************************************************)
Phase1b(i, a) ==
  /\ rnd[a] < i
  /\ [type |-> "phase1a", rnd |-> i] \in sentMsg
  /\ rnd' = [rnd EXCEPT ![a] = i]
  /\ Send([type |-> "phase1b", rnd |-> i, vrnd |-> vrnd[a], vval |-> vval[a],
           acc |-> a])
  /\ UNCHANGED <<cVars, oVars, vrnd, vval>>

(***************************************************************************)
(*`^Action $Phase2b(i, a, v)$ specifies the execution of phase 2b for      *)
(* round $i$ by acceptor $a$, upon receipt of either a phase~2a message or *)
(* a proposal (for a fast round) with value $v$.  It is described in       *)
(* Section 2.2.1 on page 5 and Section 3.1 on page 17.^'                   *)
(***************************************************************************)
Phase2b(i, a, v) ==
  /\ rnd[a] \leq i
  /\ vrnd[a] < i
  /\ \E m \in sentMsg :
      /\ m.type = "phase2a"
      /\ m.rnd = i
      /\ \/ m.val = v
         \/ /\ m.val = any
            /\ v \in proposed
  /\ rnd'  = [rnd  EXCEPT ![a] = i]
  /\ vrnd' = [vrnd EXCEPT ![a] = i]
  /\ vval' = [vval EXCEPT ![a] = v]
  /\ Send([type |-> "phase2b", rnd |-> i, val |-> v, acc |-> a])
  /\ UNCHANGED <<cVars, oVars>>

(***************************************************************************)
(*`^$accLastMsg(a)$ is defined to be the last message sent by acceptor     *)
(* $a$, if $rnd[a]>0$.^'                                                   *)
(***************************************************************************)
accLastMsg(a) ==
  IF vrnd[a] < rnd[a]
    THEN [type |-> "phase1b", rnd |-> rnd[a], vrnd |-> vrnd[a],
          vval |-> vval[a], acc |-> a]
    ELSE [type |-> "phase2b", rnd |-> rnd[a], val |-> vval[a], acc |-> a]

(***************************************************************************)
(*`^In action $AcceptorRetransmit(a)$, acceptor $a$ retransmits the last   *)
(* message it sent.^'                                                      *)
(***************************************************************************)
AcceptorRetransmit(a) ==
  /\ rnd[a] # 0
  /\ Send(accLastMsg(a))
  /\ UNCHANGED <<aVars, cVars, oVars>>

(***************************************************************************)
(*`^$AcceptorNext(a)$ is the next-state action of acceptor $a$---that is,  *)
(* the disjunct of the next-state action that represents actions of that   *)
(* acceptor.^'                                                             *)
(***************************************************************************)
AcceptorNext(a) ==
  \/ \E i \in RNum : \/ Phase1b(i, a)
                     \/ \E v \in Val : Phase2b(i, a, v)
  \/ AcceptorRetransmit(a)
-----------------------------------------------------------------------------
(***************************************************************************)
(*`^\centering \large\bf Other Actions^'                                   *)
(***************************************************************************)

(***************************************************************************)
(*`^Action $Propose(v)$ represents the proposal of a value $v$ by some     *)
(* proposer.^'                                                             *)
(***************************************************************************)
Propose(v) ==
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED <<aVars, cVars, amLeader, sentMsg, learned, goodSet>>

(***************************************************************************)
(*`^Action $Learn(v)$ represents the learning of a value $v$ by some       *)
(* learner.                                                                *)
(***************************************************************************)
Learn(v) ==
  /\ \E i \in RNum :
      \E Q \in Quorum(i) :
        \A a \in Q :
          \E m \in sentMsg : /\ m.type = "phase2b"
                             /\ m.rnd  = i
                             /\ m.val = v
                             /\ m.acc  = a
  /\ learned' = learned \cup {v}
  /\ UNCHANGED
      <<aVars, cVars, amLeader, sentMsg, proposed, goodSet>>

(***************************************************************************)
(*`^Action $LeaderSelection$ allows an arbitrary change to the values of   *)
(* $amLeader[c]$, for all coordinators $c$.  Since this action may be      *)
(* performed at any time, the specification makes no assumption about the  *)
(* outcome of leader selection.  (However, progress is guaranteed only     *)
(* under an assumption about the values of $amLeader[c]$.)^'               *)
(***************************************************************************)
LeaderSelection ==
  /\ amLeader' \in [Coord -> BOOLEAN]
  /\ UNCHANGED <<aVars, cVars, sentMsg, proposed, learned, goodSet>>


(***************************************************************************)
(*`^Action $FailOrRepair$ allows an arbitrary change to the set $goodSet$. *)
(* Since this action may be performed at any time, the specification makes *)
(* no assumption about what agents are good.  (However, progress is        *)
(* guaranteed only under an assumption about the value of $goodSet$.)^'    *)
(***************************************************************************)
FailOrRepair ==
  /\ goodSet' \in SUBSET (Coord \cup Acc)
  /\ UNCHANGED <<aVars, cVars, amLeader, sentMsg, proposed, learned>>

(***************************************************************************)
(*`^Action $LoseMsg(m)$ removes message $m$ from $sentMsg$.  It is always  *)
(* enabled unless $m$ is the last message sent by an acceptor or           *)
(* coordinator in $goodSet$.  Hence, the only assumption the               *)
(* specification makes about message loss is that the last message sent by *)
(* an agent in $goodSet$ is not lost.  Because $sentMsg$ includes          *)
(* messages in an agent's output buffer, this effectively means that a     *)
(* non-failed process always has the last message it sent in its output    *)
(* buffer, ready to be retransmitted.^'                                    *)
(***************************************************************************)
LoseMsg(m) ==
  /\ ~ \/ /\ m.type \in {"phase1a", "phase2a"}
          /\ m = coordLastMsg(CoordOf(m.rnd))
          /\ CoordOf(m.rnd) \in goodSet
          /\ amLeader[CoordOf(m.rnd)]
       \/ /\ m.type \in {"phase1b", "phase2b"}
          /\ m = accLastMsg(m.acc)
          /\ m.acc \in goodSet
  /\ sentMsg' = sentMsg \ {m}
  /\ UNCHANGED <<aVars, cVars, oVars>>

(***************************************************************************)
(*`^Action $OtherAction$ is the disjunction of all actions other than ones *)
(* performed by acceptors or coordinators, plus the $LeaderSelection$      *)
(* action (which represents leader-selection actions performed by the      *)
(* coordinators).^'                                                        *)
(***************************************************************************)
OtherAction ==
  \/ \E v \in Val : Propose(v) \/ Learn(v)
  \/ LeaderSelection \/ FailOrRepair
  \/ \E m \in sentMsg : LoseMsg(m)


(***************************************************************************)
(*`^$Next$ is the algorithm's complete next-state action.^'                *)
(***************************************************************************)
Next ==
  \/ \E c \in Coord : CoordNext(c)
  \/ \E a \in Acc : AcceptorNext(a)
  \/ OtherAction
-----------------------------------------------------------------------------
(***************************************************************************)
(*`^\centering\large\bf Temporal Formulas^'                                *)
(***************************************************************************)

(***************************************************************************)
(*`^Formula $Fairness$ specifies the fairness requirements as the          *)
(* conjunction of weak fairnes formulas.  Intuitively, it states           *)
(* approximately the following:                                            *)
(* \begin{itemize}                                                         *)
(* \item[] A coordinator $c$ in $goodSet$ must perform some action if it   *)
(* can, and it must perform a $Phase1a(c,i)$ action for a classic round    *)
(* $i$ if it can.                                                          *)
(*                                                                         *)
(* \item[] An acceptor in $goodSet$ must perform some action if it can.    *)
(*                                                                         *)
(* \item[] A value that can be learned must be learned.                    *)
(* \end{itemize}                                                           *)
(* It is not obvious that these fairness requirements suffice to imply the *)
(* progress property, and that fairness of each individual acceptor and    *)
(* coordinator action is not needed.  Part of the reason is that formula   *)
(* $Fairness$ does not allow an agent in $goodSet$ to do nothing but       *)
(* $Retransmit$ actions if another of its actions is enabled, since all    *)
(* but the first retransmission would be a stuttering step, and weak       *)
(* fairness of an action $A$ requires a non-stuttering $A$ step to occur   *)
(* if it is enabled.^'                                                     *)
(***************************************************************************)
Fairness ==
  /\ \A c \in Coord :
      /\ WF_vars((c \in goodSet) /\ CoordNext(c))
      /\ WF_vars((c \in goodSet) /\ (\E i \in ClassicNum : Phase1a(c, i)))
  /\ \A a \in Acc : WF_vars((a \in goodSet) /\ AcceptorNext(a))
  /\ \A v \in Val : WF_vars(Learn(v))

(***************************************************************************)
(*`^Formula $Spec$ is the complete specification of the Fast Paxos         *)
(* algorithm.^'                                                            *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(*`^$Nontriviality$ asserts that every learned value has been proposed,    *)
(* and $Consistency$ asserts that at most one value has been learned.      *)
(* The Nontriviality and Consistency conditions for consensus              *)
(* (Section 2.1) are equivalent to the invariance of these                 *)
(* state predicates.^'                                                     *)
(***************************************************************************)
Nontriviality == learned \subseteq proposed
Consistency   == Cardinality(learned) \leq 1

(***************************************************************************)
(*`^The following theorem asserts that the state predicates $TypeOK$,      *)
(* $Nontriviality$, and $Consistency$ are invariants of specification      *)
(* $Spec$, which implies that $Spec$ satisfies the safety properties of a  *)
(* consensus algorithm.  It was checked by the TLC model checker on models *)
(* that were too small to find a real bug in the algorithm but would have  *)
(* detected most simple errors in the specification.^'                     *)
(***************************************************************************)
THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)

(***************************************************************************)
(*`^Because the specification does not explicitly mention proposers and    *)
(* learners, condition $LA(p,l,c,Q)$ described on page 10 of Section 2.3.1 *)
(* is replaced by $LA(c,Q)$, which depends only on $c$ and $Q$.  Instead   *)
(* of asserting that some particular proposer $p$ has proposed a value, it *)
(* asserts that some value has been proposed.^'                            *)
(***************************************************************************)
LA(c, Q) ==
  /\ {c} \cup Q \subseteq goodSet
  /\ proposed # {}
  /\ \A ll \in Coord : amLeader[ll] \equiv (c = ll)

(***************************************************************************)
(*`^The following theorem asserts that $Spec$ satisfies the progress       *)
(* property of Fast Paxos, described in Fast Paxos, Sections 2.3           *)
(* and 3.3.  The temporal formula $<>[]LA(c,Q)$                            *)
(* asserts that $LA(c,Q)$ holds from some time on,                         *)
(* and $<>(learned \neq \{\})$                                             *)
(* asserts that some value is eventually learned.                          *)
(***************************************************************************)
THEOREM /\ Spec
        /\ \E Q \in SUBSET Acc :
            /\ \A i \in ClassicNum : Q \subseteq Quorum(i)
            /\ \E c \in Coord : <>[]LA(c, Q)
        => <>(learned # {})
=============================================================================
