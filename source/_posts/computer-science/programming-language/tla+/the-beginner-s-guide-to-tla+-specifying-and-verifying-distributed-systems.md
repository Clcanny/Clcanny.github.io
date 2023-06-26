---
layout: post
title: >-
  The Beginner's Guide to TLA+: Specifying and Verifying Distributed Systems
date: 2023-06-26 23:15:00
categories:
  - [Computer Science, Programming Language, TLA+]
---

[The TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html) is excellent material for learning TLA+. However, the most effective way to learn something new is to try it out, fail, and try again. This post is a record of what I've learned from trying out some of the TLA+ examples from that course.

## Running TLA+ from the Command Line on Linux

```bash
docker run -it --rm amazoncorretto:11 bash
yum install -y git
git clone https://github.com/pmer/tla-bin.git
cd tla-bin
./download_or_update_tla.sh --nightly
./install.sh
tlc -help
```

## SimpleProgram

```cpp
int i = 0;
void main() {
  i = someNumber();
  i = i + 1;
}
```

```tla+
--------------------------- MODULE SimpleProgram ---------------------------
\* SimpleProgram.tla
EXTENDS Integers
VARIABLES i, pc

Init ==
  /\ pc = "start"
  /\ i = 0

PhaseMiddle ==
  /\ pc = "start"
  /\ pc' = "middle"
  /\ i' \in 1..1000

PhaseDone ==
  /\ pc = "middle"
  /\ pc' = "done"
  /\ i' = i + 1

Next ==
  \/ PhaseMiddle
  \/ PhaseDone
  \* The simplest formula that does not equal true
  \* for any values of pc, i, pc', i'.
  \* This formula essentially means "there are no possible next states".
  \/ FALSE
============================================================================
```

```cfg
\* SimpleProgram.cfg
INIT
Init

NEXT
Next
```

```bash
tlc SimpleProgram.tla -config SimpleProgram.cfg -deadlock
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 0.0
# 2001 states generated, 2001 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 3.
```

## Die Hard

```tla+
--------------------------- MODULE DieHard ---------------------------------
\* DieHard.tla
EXTENDS Integers
VARIABLES three_gallon_jug, five_gallon_jug

Init ==
  /\ three_gallon_jug = 0
  /\ five_gallon_jug = 0

MakeThreeGallonJugFull ==
  /\ three_gallon_jug' = 3
  /\ five_gallon_jug' = five_gallon_jug

MakeFiveGallonJugFull ==
  /\ three_gallon_jug' = three_gallon_jug
  /\ five_gallon_jug' = 5

MakeThreeGallonJugEmpty ==
  /\ three_gallon_jug' = 0
  /\ five_gallon_jug' = five_gallon_jug

MakeFiveGallonJugEmpty ==
  /\ three_gallon_jug' = three_gallon_jug
  /\ five_gallon_jug' = 0

PourFromFiveGallonJugToThreeGallonJug ==
  /\ three_gallon_jug' =
    IF three_gallon_jug + five_gallon_jug < 3
      THEN three_gallon_jug + five_gallon_jug
      ELSE 3
  /\ five_gallon_jug' =
    IF three_gallon_jug + five_gallon_jug < 3
      THEN 0
      ELSE five_gallon_jug - (3 - three_gallon_jug)

PourFromThreeGallonJugToFiveGallonJug ==
  /\ three_gallon_jug' =
    IF five_gallon_jug + three_gallon_jug < 5
      THEN 0
      ELSE three_gallon_jug - (5 - five_gallon_jug)
  /\ five_gallon_jug' =
    IF five_gallon_jug + three_gallon_jug < 5
      THEN five_gallon_jug + three_gallon_jug
      ELSE 5

Next ==
  \/ MakeThreeGallonJugFull
  \/ MakeFiveGallonJugFull
  \/ MakeThreeGallonJugEmpty
  \/ MakeFiveGallonJugEmpty
  \/ PourFromFiveGallonJugToThreeGallonJug
  \/ PourFromThreeGallonJugToFiveGallonJug

TypeOK ==
  /\ three_gallon_jug \in 0..3
  /\ five_gallon_jug \in 0..5

FiveGallonJugIsFour ==
  five_gallon_jug /= 4
============================================================================
```

```cfg
\* DieHard.cfg
INIT
Init

NEXT
Next

INVARIANT
TypeOK
FiveGallonJugIsFour
```

```bash
tlc DieHard.tla -config DieHard.cfg
# Error: Invariant FiveGallonJugIsFour is violated.
# Error: The behavior up to this point is:
# State 1: <Initial predicate>
# /\ three_gallon_jug = 0
# /\ five_gallon_jug = 0
#
# State 2: <MakeFiveGallonJugFull line 15, col 3 to line 16, col 25 of module DieHard>
# /\ three_gallon_jug = 0
# /\ five_gallon_jug = 5
#
# State 3: <PourFromFiveGallonJugToThreeGallonJug line 27, col 3 to line 34, col 51 of module DieHard>
# /\ three_gallon_jug = 3
# /\ five_gallon_jug = 2
#
# State 4: <MakeThreeGallonJugEmpty line 19, col 3 to line 20, col 39 of module DieHard>
# /\ three_gallon_jug = 0
# /\ five_gallon_jug = 2
#
# State 5: <PourFromFiveGallonJugToThreeGallonJug line 27, col 3 to line 34, col 51 of module DieHard>
# /\ three_gallon_jug = 2
# /\ five_gallon_jug = 0
#
# State 6: <MakeFiveGallonJugFull line 15, col 3 to line 16, col 25 of module DieHard>
# /\ three_gallon_jug = 2
# /\ five_gallon_jug = 5
#
# State 7: <PourFromFiveGallonJugToThreeGallonJug line 27, col 3 to line 34, col 51 of module DieHard>
# /\ three_gallon_jug = 3
# /\ five_gallon_jug = 4
```

## Transaction Commit

```tla+
--------------------------- MODULE TransactionCommit -----------------------
\* TransactionCommit.tla
EXTENDS Integers
CONSTANTS RM
VARIABLES rmState

\* The TLA+ syntax for an array expression:
\* [variable \in set |-> expression]
\*
\* https://www.learntla.com/core/functions.html#function
\* First of all, throw away the programming definition of "function".
\* The closest thing TLA+ has to a programmatic function are operators.
\* A function follows the mathematical definition,
\* a mapping of values in one set to another set.
\* e.g., F == [x \in S |-> expr]
\* The set we're mapping from, S, is the domain of the function,
\* and can be retrieved by writing DOMAIN F.
\*
\* https://www.learntla.com/core/functions.html#using-functions
\* Why functions over operators?
\* We rarely use functions for computations -
\* operators are far superior for that.
\* Functions are important as values.
\* We can assign them to variables and manipulate them like any other value.
Init == rmState = [rm \in RM |-> "working"]

Prepare(r) ==
  /\ rmState[r] = "working"
  \* rmState'[r] = "prepared" is wrong.
  \* This formula says the value of rmState[r] in the new state is "prepared".
  \* It says nothing about the value of rmState[s] in the new state
  \* for an RM s with s != r.
  \*
  \* rmState' = [s \in RM |-> IF s = r THEN "prepared" ELSE rmState[s]]
  \* This is correct, but it's too long-winded.
  \* We need a shorter way to write this expression.
  \* TLA+ provides this EXCEPT construct. Everyone hates it.
  \* What does the exclamation point (usually read as bang) mean?
  \* It means nothing. It's just syntax. But you'll get used to it.
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
DecideToCommit(r) ==
  /\ rmState[r] = "prepared"
  \* We have to change the bound variable r to some other variable like s
  \* to avoid a name conflict with this r.
  \*
  \* The scope of \A and \E extends as far as possible.
  \* The expression \A x \in S: ... extends
  \* to the end of its enclosing expression unless explicitly ended
  \* - by parentheses, (\A x \in S: ...)
  \* - or by similar brackets or braces
  \* - or by the end of a list item (which adds implicit parentheses),
  \*   /\
  \*   /\ \A x \in S: ...
  \*   /\
  \* - e.g., This expression
  \*      \A x \in S: ...
  \*   /\ \A x \in T: ...
  \*   is parsed like this \A x \in S: (... \A x \in T: ...).
  /\ (\A s \in RM: rmState[s] \in {"prepared", "committed"})
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
DecideToAbort(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  \* DecideToAbort(r) depends on the states of all the resource managers.
  \* How can this be implemented?
  \* What programming language allows a single step
  \* to examine the states of a whole set of processes?
  \* We don't care.
  \* We're writing a spec of what transaction commit should do,
  \* not how it’s implemented.
  /\ (\A s \in RM: rmState[s] /= "committed")
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
Next ==
  \E r \in RM:
    \/ Prepare(r)
    \/ DecideToCommit(r)
    \/ DecideToAbort(r)

TypeOK ==
  \* https://www.learntla.com/core/functions.html#using-functions
  \* In a spec I once wrote, I had to assign tasks to CPUs.
  \* Some tasks needed to be assigned to many CPUs,
  \* but each CPU should only have one task.
  \* In that spec, the best solution was to store assignments as functions,
  \* where each task mapped to a set of CPUs.
  \* variables
  \*   assignments = [t \in Tasks |-> {}]
  \* Then I could write assignment[t] := assignment[t] \union {cpu}
  \* to assign cpu to task t.
  \* For my invariant, I said no two tasks shared a CPU assignment.
  \* OnlyOneTaskPerCpu ==
  \*   \A t1, t2 \in Tasks, c \in CPU:
  \*     /\ (t1 # t2)
  \*     /\ c \in assignments[t1]
  \*     => c \notin assignments[t2]
  \*
  \* https://www.learntla.com/core/functions.html#function-sets
  \* The syntax for function sets is [S -> T]
  \* (T is sometimes referred to as the "codomain") and
  \* is "every function where the domain is S and all of the values are in T."
  \* In the prior task example, assignments was always a function
  \* in the function set [Tasks -> SUBSET CPUs].
  \* A function set of form [A -> B] will have B^A elements in it.
  \* If there were two tasks and three CPUs,
  \* that would be (2^3)^2 = 64 (B = 8, A = 2) possible functions.
  \* A good way to remember this: [1..n -> BOOLEAN] is
  \* the set of all binary strings of length n,
  \* and we know there are 2^n such strings.
  \*
  \* The set of all arrays indexed by elements of RM
  \* with values in {"working", "prepared", "committed", "aborted"}.
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Consistent ==
  \* An abbreviation for \A r1 \in RM: \A r2 \in RM:
  \A r1, r2 \in RM:
    ~ /\ rmState[r1] = "aborted"
      /\ rmState[r2] = "committed"
============================================================================
```

```cfg
\* TransactionCommit.cfg
CONSTANT
RM = {"rm1", "rm2", "rm3"}

INIT
Init

NEXT
Next

INVARIANT
TypeOK
Consistent
```

```bash
tlc TransactionCommit.tla -config TransactionCommit.cfg -deadlock
# # Always be suspicious of success.
# # Check the statistics of the TLC run.
# # Did TLC find a reasonable number of states
# # that can be reached by behaviors?
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 1.1E-16
# 94 states generated, 34 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 7.
```

## Two Phase

```tla
--------------------------- MODULE TwoPhase --------------------------------
\* TwoPhase.tla
EXTENDS Integers
CONSTANTS RM
VARIABLES rmState, tmState, tmPrepared, msgs

\* https://www.learntla.com/core/functions.html#structures
\* In TLA+, this is the struct:
\* st == [a |-> 1, b |-> {}]
\* You index structs the same way you do sequences so st["a"] = 1.
\* You can also write it in a more "object" like with a dot instead: st.a = 1.
\* We want some way to generate sets of structs,
\* so we can stick them in our type invariants. Here’s how:
\* BankTransactionType == [acct: Accounts,
\*                         amnt: 1..10,
\*                         type: {"deposit", "withdraw"}]
\* This is the set of all structures
\* where s.acct \in Accounts, s.amnt \in 1..10, etc.
\*
\* https://www.learntla.com/core/functions.html#getting-a-struct-s-keys
\* Both sequences and structures are just syntactic sugar.
\* TLA+ has only two "real" collections: sets and functions.
\* Sequences and structures are both particular classes of functions.
\*
\* https://www.learntla.com/core/functions.html#function
\* F == [x \in S |-> expr]
\* The set we're mapping from, S, is the domain of the function,
\* and can be retrieved by writing DOMAIN F.
\* That's why we could also use DOMAIN with sequences and structures:
\* 1. A sequence is just a function where the domain is 1..n.
\* 2. A struct is just a function where the domain is a set of strings.
\*
\* https://lamport.azurewebsites.net/video/video6-script.pdf
\* A record corresponds roughly to a Struct in C.
\* The definition r == [prof |-> "Fred", num |-> 42]
\* defines r to be a record with two fields prof and num.
\* This record is actually a function, let's call it f,
\* whose domain is the set containing the two strings prof and num,
\* such that f of the string prof equals the string "Fred" and
\* f of the string num equals the number 42.
\*
\* [f EXCEPT !["prof"] = "Red"]
\* This EXCEPT expression equals the record that's the same as f
\* except its prof field equals the string Red.
\* It can be abbreviated as [f EXCEPT !.prof = "Red"]
Messages ==
         [type: {"Prepared"}, rm: RM]
  \* {[type |-> "Commit"], [type |-> "Abort"]}
  \* Each record represents a message sent by the TM to all RMs.
  \union [type: {"Commit", "Abort"}]

Init ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

TMRcvPreparedMsg(r) ==
  \* These two conjunctions have no primes.
  \* They're conditions on the first state of a step.
  \* They're called enabling conditions of the formula.
  \* Enabling conditions should almost always go at the beginning of
  \* an action formula – a formula that contains primed variables.
  \* That makes the formula easier to understand,
  \* and TLC often can't handle the action formula if you don't.
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  \* An action formula.
  /\ tmPrepared' = tmPrepared \union {r}
  \* It asserts rmState, tmState, and msgs are left unchanged,
  \* which is equivalent to
  \* /\ rmState' = rmState
  \* /\ tmState' = tmState
  \* /\ msgs' = msgs
  \* The step doesn't remove the message from msgs.
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMDecideToCommit ==
  /\ tmState = "init"
  /\ RM \subseteq tmPrepared
  /\ tmState' = "done"
  \* Since two-phase commit requires no assumptions about the order in which
  \* different messages are received, the simplest natural representation
  \* is to let msgs be a single set containing all messages in transit.
  \* Receiving a message removes it from the set msgs.
  \* There's a simpler method that's not obvious to most people.
  \* It's to let msgs be the set of all messages that have ever been sent.
  \* So the action of receiving a message
  \* doesn't remove the message from the set.
  \* 1. One advantage is that a single message in msgs
  \*    can be received by several processes.
  \* 2. It also means that a process can
  \*    received the same message multiple times.
  \*    This can happen with real message passing, and it’s useful to know that
  \*    the two-phase commit protocol still works even if it does happen.
  /\ msgs' = msgs \union [type: {"Commit"}]
  /\ UNCHANGED <<rmState, tmPrepared>>

TMDecideToAbort ==
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ msgs' = msgs \union [type: {"Abort"}]
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \union [type: {"Prepared"}, rm: {r}]
  /\ UNCHANGED <<tmState, tmPrepared>>

RMDecideToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) ==
  /\ rmState[r] = "prepared"
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
  \/ TMDecideToCommit
  \/ TMDecideToAbort
  \/ (\E r \in RM:
        \/ TMRcvPreparedMsg(r)
        \/ RMPrepare(r)
        \/ RMDecideToAbort(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r))

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "done"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

Consistent == \A r1, r2 \in RM:
  ~ (/\ rmState[r1] = "committed"
     /\ rmState[r2] = "aborted")
============================================================================
```

```cfg
\* TwoPhase.cfg
CONSTANT
RM = {"rm1", "rm2", "rm3"}

INIT
Init

NEXT
Next

INVARIANT
TypeOK
Consistent
```

```bash
tlc TwoPhase.tla -config TwoPhase.cfg -deadlock
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 8.1E-15
# 810 states generated, 288 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 11.
```

## Synod Basic Protocol

```tla
--------------------------- MODULE SynodBasicProtocol ----------------------
\* SynodBasicProtocol.tla
EXTENDS Integers, FiniteSets, TLC
CONSTANTS PRIESTS, DECREES, BALLOT_IDS
VARIABLES priestStatus, ledgers, usedBallotIds, msgs

\* https://github.com/tlaplus/tlaplus/issues/404
SYMM == Permutations(PRIESTS) \union Permutations(DECREES)
\* I am uncertain whether or not BALLOT_IDS qualifies as a symmetry set.
\* \union Permutations(BALLOT_IDS)

\* This ASSUME statement asserts assumptions being made about the constants.
ASSUME
  /\ BALLOT_IDS \subseteq Nat
  /\ IsFiniteSet(BALLOT_IDS)

BlankDecree == "BLANK"

GetQuorum(ballotId) ==
  {m.to: m \in {m \in msgs: m.type = "BeginBallot" /\ m.ballotId = ballotId}}

GetDecree(ballotId) ==
  (CHOOSE m \in msgs: m.type = "BeginBallot" /\ m.ballotId = ballotId).decree

Init ==
  /\ priestStatus =
    [
      p \in PRIESTS |->
      [
        lastTriedBallotId |-> -1,
        prevVote          |->
          [priest |-> p, ballotId |-> -1, decree |-> BlankDecree],
        nextBallotId      |-> -1
      ]
    ]
  /\ ledgers = [p \in PRIESTS |-> [decree |-> BlankDecree]]
  /\ usedBallotIds = {}
  /\ msgs = {}

\* Step (1)
\* Priest $p$ chooses a new ballot number $b$
\* greater than $\operatorname{lastTried}(p)$,
\* sets $\operatorname{lastTried}(p)$ to $b$,
\* and sends a $\operatorname{NextBallot}(b)$ message
\* to some set of priests.
SendNextBallotMsg(p) ==
  \* This set minus operator is defined as follows.
  \* For any sets S and T,
  \* S set minus T is the set of all elements in S that are not in T.
  \E b \in BALLOT_IDS \ usedBallotIds:
    /\ ledgers[p].decree = BlankDecree
    \* The following use of CHOOSE is incorrect:
    \* b == CHOOSE n \in availBallotIds: n > priestStatus[p].lastTriedBallotId
    \* Because there may be multiple values in availBallotIds that
    \* satisfy n > priestStatus[p].lastTriedBallotId.
    \* Instead, EXISTS should be used here.
    \* The difference between CHOOSE and EXISTS will be explained later.
    /\ b > priestStatus[p].lastTriedBallotId
    /\ priestStatus' =
      [priestStatus EXCEPT ![p].lastTriedBallotId = b]
      \* The expression above is a shorter way to say
      \* the same thing as the next expression.
      \* [
      \*   priestStatus EXCEPT ![p] =
      \*     [priestStatus[p] EXCEPT !.lastTriedBallotId = b]
      \* ]
    /\ usedBallotIds' = usedBallotIds \union {b}
    /\ msgs' = msgs \union
      {[
        type     |-> "NextBallot",
        ballotId |-> b
      ]}
    /\ UNCHANGED <<ledgers>>

\* Step (2)
\* Upon receipt of a $\operatorname{NextBallot}(b)$ message from $p$
\* with $b > \operatorname{nextBal}(q)$,
\* priest $q$ sets $\operatorname{nextBal}(q)$ to $b$ and
\* sends a $\operatorname{LastVote}(b, v)$ message to $p$,
\* where $v$ equals $\operatorname{prevVote}(q)$.
ReceiveNextBallotMsg(q) ==
  \E b \in BALLOT_IDS:
    /\ [type |-> "NextBallot", ballotId |-> b] \in msgs
    /\ b > priestStatus[q].nextBallotId
    /\ priestStatus' =
      [priestStatus EXCEPT ![q].nextBallotId = b]
      \* The expression above is a shorter way to say
      \* the same thing as the next expression.
      \* [priestStatus EXCEPT ![q] = [priestStatus[q] EXCEPT !.nextBallotId = b]]
    /\ msgs' = msgs \union {[
        type     |-> "LastVote",
        ballotId |-> b,
        vote     |-> priestStatus[q].prevVote
      ]}
    /\ UNCHANGED <<ledgers, usedBallotIds>>

\* Step (3)
\* After receiving a $\operatorname{LastVote}(b, v)$ message
\* from every priest in some majority set $Q$,
\* where $b = \operatorname{lastTried}(p)$,
\* priest $p$ initiates a new ballot
\* with number $b$, quorum $Q$, and decree $d$,
\* where $d$ is chosen to satisfy $\operatorname{B3}$.
\* He then sends a $\operatorname{BeginBallot}(b, d)$ message
\* to every priest in $Q$.
ReceiveLastVoteMsg(p) ==
  \* SUBSET PRIESTS is the set of all subsets of the set PRIESTS.
  \* Mathematicians call it the powerset of PRIESTS and
  \* write it \mathcal{P}(Acceptor).
  \E majority \in SUBSET PRIESTS, dec \in DECREES:
    \* The LET clause makes these definitions local to the let-in expression.
    \* The defined identifiers can be used only in the expression.
    LET
      b == priestStatus[p].lastTriedBallotId
      \* https://www.learntla.com/core/operators.html#map-and-filter
      lastVoteMsgs ==
        {
          m \in msgs:
            /\ m.type = "LastVote"
            /\ m.ballotId = b
            /\ m.vote.priest \in majority
        }
      v ==
        (CHOOSE m \in lastVoteMsgs:
          \A n \in lastVoteMsgs:
            m.vote.ballotId >= n.vote.ballotId).vote
      d ==
        IF v.ballotId = -1 /\ v.decree = BlankDecree
          THEN dec
          ELSE v.decree
    IN
      /\ {m \in msgs: m.type = "BeginBallot" /\ m.ballotId = b} = {}
      \* https://www.learntla.com/core/operators.html#map-and-filter
      /\ {m.vote.priest: m \in lastVoteMsgs} = majority
      /\ Cardinality(majority) * 2 > Cardinality(PRIESTS)
      /\ msgs' = msgs \union
        [
          type     : {"BeginBallot"},
          ballotId : {b},
          decree   : {d},
          to       : majority
        ]
      /\ UNCHANGED <<priestStatus, ledgers, usedBallotIds>>

\* Step (4)
\* Upon receipt of a $\operatorname{BeginBallot}(b, d)$ message
\* with $b = \operatorname{nextBal}(q)$,
\* priest $q$ casts his vote in ballot number $b$,
\* sets $\operatorname{prevVote}(q)$ to this vote,
\* and sends a $\operatorname{Voted}(b, q)$ message to $p$.
ReceiveBeginBallotMsg(q) ==
  \E d \in DECREES:
    LET
      b == priestStatus[q].nextBallotId
    IN
      /\
        [
          type     |-> "BeginBallot",
          ballotId |-> b,
          decree   |-> d,
          to       |-> q
        ] \in msgs
      /\ priestStatus' =
        [
          priestStatus EXCEPT ![q].prevVote.priest = q,
                              ![q].prevVote.ballotId = b,
                              ![q].prevVote.decree = d
        ]
        \* The expression above is a shorter way to say
        \* the same thing as the next expression.
        \* [
        \*   priestStatus EXCEPT ![q] =
        \*     [
        \*       priestStatus[q] EXCEPT !.prevVote =
        \*         [priest |-> q, ballotId |-> b, decree |-> d]
        \*     ]
        \* ]
      /\ msgs' = msgs \union
        {[
          type     |-> "Voted",
          ballotId |-> b,
          from     |-> q
        ]}
      /\ UNCHANGED <<ledgers, usedBallotIds>>

\* Step (5)
\* If $p$ has received a $\operatorname{Voted}(b, q)$ message
\* from every priest $q$ in $Q$ (the quorum for ballot number $b$),
\* where $b = \operatorname{lastTried}(p)$,
\* then he writes $d$ (the decree of that ballot) in his ledger and
\* sends a $\operatorname{Success}(d)$ message to every priest.
ReceiveVotedMsg(p) ==
  LET
    b == priestStatus[p].lastTriedBallotId
    votedMsgs ==
      {m \in msgs: m.type = "Voted" /\ m.ballotId = b}
  IN
    /\ GetQuorum(b) # {}
    /\ {m.from: m \in votedMsgs} = GetQuorum(b)
    /\ ledgers[p].decree = BlankDecree
    /\ ledgers' = [ledgers EXCEPT ![p] = [decree |-> GetDecree(b)]]
    /\ msgs' = msgs \union
      {[
        type     |-> "Success",
        ballotId |-> b,
        decree   |-> GetDecree(b)
      ]}
    /\ UNCHANGED <<priestStatus, usedBallotIds>>

\* Step (6)
\* Upon receiving a $\operatorname{Success}(d)$ message,
\* a priest enters decree $d$ in his ledger.
ReceiveSuccessMsg(q) ==
  LET
    successMsgs == {m \in msgs: m.type = "Success"}
    decrees == {m.decree: m \in successMsgs}
  IN
    /\ decrees # {}
    /\ ledgers[q].decree = BlankDecree
    /\ ledgers' =
        \* The Difference Between CHOOSE and EXISTS, and When to Use CHOOSE
        \* https://lamport.azurewebsites.net/video/video7-script.pdf
        \*
        \* x' \in 1..99
        \* The formula x' in the set 1..99 allows the value of x in the next
        \* state to be any of the 99 numbers from 1 to 99.
        \*
        \* CHOOSE i \in 1..99: TRUE
        \* The above expression equals an unspecified integer
        \* between 1 and 99. We don't know which one.
        \* It might or might not equal 37; the semantics of TLA+ don't say.
        \*
        \* However, there is no nondeterminism in a mathematical expression.
        \* Any expression always equals itself, including a CHOOSE expression.
        \* So this CHOOSE expression always equals itself:
        \* (CHOOSE i \in 1..99: TRUE) = (CHOOSE i \in 1..99: TRUE)
        \* If this CHOOSE expression equals 37 today,
        \* it will still equal 37 next week.
        \* TLC will always get the same number
        \* when it evaluates this expression.
        \* But you shouldn't care what number.
        \*
        \* x' = CHOOSE i \in 1..99: TRUE
        \* The formula x' equals this CHOOSE expression allows
        \* the value of x in the next state to be some particular number
        \* between 1 and 99 — perhaps 37.
        \* There's no reason why you'd ever want to write something like this.
        \* You should write this CHOOSE v \in S: P expression only when
        \* there's exactly one value v in S satisfying formula P.
        \* Or when it's part of a larger expression whose value
        \* doesn't depend on which possible value of v is chosen.
        \* e.g., (CHOOSE m \in mset: m.bal = maxbal).val
        \* This CHOOSE expression can allow
        \* more than one possible choice for m.
        \* However, in any reachable state of the algorithm,
        \* all possible choices of m have the same value of m.val.
        [ledgers EXCEPT ![q] = [decree |-> CHOOSE d \in decrees: TRUE]]
    /\ UNCHANGED <<priestStatus, usedBallotIds, msgs>>

Next == \E p \in PRIESTS:
  \/ SendNextBallotMsg(p)
  \/ ReceiveNextBallotMsg(p)
  \/ ReceiveLastVoteMsg(p)
  \/ ReceiveBeginBallotMsg(p)
  \/ ReceiveVotedMsg(p)
  \/ ReceiveSuccessMsg(p)

TypeOK ==
  LET
    validBallotIds == {-1} \union BALLOT_IDS
    validDecrees == {BlankDecree} \union DECREES
  IN
    /\ DOMAIN priestStatus = PRIESTS
    /\ \A p \in PRIESTS:
      priestStatus[p] \in
        [
          lastTriedBallotId : validBallotIds,
          prevVote          :
            [
              priest   : PRIESTS,
              ballotId : validBallotIds,
              decree   : validDecrees
            ],
          nextBallotId      : validBallotIds
        ]
    /\ ledgers \in [PRIESTS -> [decree: validDecrees]]
    /\ usedBallotIds \subseteq BALLOT_IDS
    /\ msgs \subseteq
             [type: {"NextBallot"}, ballotId: BALLOT_IDS]
      \union [type     : {"LastVote"},
              ballotId : BALLOT_IDS,
              vote     : [priest   : PRIESTS,
                          ballotId : validBallotIds,
                          decree   : validDecrees]]
      \union [type     : {"BeginBallot"},
              ballotId : BALLOT_IDS,
              decree   : DECREES,
              to       : PRIESTS]
      \union [type     : {"Voted"},
              ballotId : BALLOT_IDS,
              from     : PRIESTS]
      \union [type     : {"Success"},
              ballotId : BALLOT_IDS,
              decree   : DECREES]

B1Consistent ==
  \* $\operatorname{B1}(\mathcal{B})$
  \* Each ballot in $\mathcal{B}$ has a unique ballot number.
  /\ \A p1, p2 \in {p \in PRIESTS: priestStatus[p].lastTriedBallotId # -1}:
    \/ p1 = p2
    \/ priestStatus[p1].lastTriedBallotId # priestStatus[p2].lastTriedBallotId
  /\ \A m1, m2 \in {m \in msgs: m.type = "BeginBallot"}:
    \/ m1.decree = m2.decree
    \/ m1.ballotId # m2.ballotId

B2Consistent ==
  \* $\operatorname{B2}(\mathcal{B})$
  \* The quorums of any two ballots in $\mathcal{B}$
  \* have at least one priest in common.
  \A m1, m2 \in {m \in msgs: m.type = "BeginBallot"}:
    GetQuorum(m1.ballotId) \intersect GetQuorum(m2.ballotId) # {}

B3Consistent ==
  \* $\operatorname{B3}(\mathcal{B})$
  \* For every ballot $B$ in $\mathcal{B}$,
  \* if any priest in $B$'s quorum voted in an earlier ballot in $\mathcal{B}$,
  \* then the decree of $B$ equals
  \* the decree of the latest of those earlier ballots.
  \A beginBallotMsg \in {m \in msgs: m.type = "BeginBallot"}:
    LET
      quorum == GetQuorum(beginBallotMsg.ballotId)
      votedMsgs ==
        {
          m \in msgs:
            /\ m.type = "Voted"
            /\ m.ballotId < beginBallotMsg.ballotId
            /\ m.from \in quorum
        }
    IN
      \/ votedMsgs = {}
      \/
        LET
          latestEarlierBallotId ==
            (CHOOSE latestMsg \in votedMsgs:
              \A m \in votedMsgs:
                latestMsg.ballotId >= m.ballotId).ballotId
          latestEarlierDecree ==
            (CHOOSE m \in msgs:
              /\ m.type = "BeginBallot"
              /\ m.ballotId = latestEarlierBallotId).decree
        IN
          beginBallotMsg.decree = latestEarlierDecree

LemmaConsistent ==
  \* Lemma
  \* To show that these conditions imply consistency,
  \* the Paxons first showed that
  \* $\operatorname{B1}(\mathcal{B})$ – $\operatorname{B3}(\mathcal{B})$
  \* imply that, if a ballot $B$ in $\mathcal{B}$ is successful,
  \* then any later ballot in $\mathcal{B}$ is for the same decree as $B$.
  \A m1 \in {m \in msgs: m.type = "Success"}:
    \A m2 \in {m \in msgs: m.type = "BeginBallot" /\ m.ballotId > m1.ballodId}:
      m2.decree = m1.decree

Theorem1Consistent ==
  \* Theorem 1
  \* Any two successful ballots are for the same decree.
  \A m1, m2 \in {m \in msgs: m.type = "Success"}: m1.decree = m2.decree

LedgerConsistent ==
  \A p1, p2 \in PRIESTS:
    \/ ledgers[p1].decree = BlankDecree
    \/ ledgers[p2].decree = BlankDecree
    \/ ledgers[p1] = ledgers[p2]

Consistent ==
  /\ B1Consistent
  /\ B2Consistent
  /\ B3Consistent
  /\ Theorem1Consistent
  /\ LedgerConsistent
============================================================================
```

```cfg
\* SynodBasicProtocol-WithoutSymmetrySets.cfg
CONSTANT
PRIESTS = {p1, p2, p3}
DECREES = {d1, d2, d3}
\* Even a modest increase in the range of BALLOT_IDS,
\* from 0..2 to 0..10,
\* can significantly increase the number of possible distinct states.
BALLOT_IDS = {0, 1, 2}

INIT
Init

NEXT
Next

INVARIANT
TypeOK
Consistent
```

```bash
export JAVA_OPTS="-Xms80g -XX:+UseParallelGC"
tlc SynodBasicProtocol.tla -config SynodBasicProtocol-WithoutSymmetrySets.cfg -deadlock -workers 40
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 6.2E-5
#   based on the actual fingerprints:  val = 9.9E-6
# 81223510 states generated, 18306583 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 28.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 21 and the 95th percentile is 3).
# Finished in 07min 49s at (2023-07-08 21:12:20)
```

```cfg
\* SynodBasicProtocol-WithSymmetrySets.cfg
CONSTANT
\* https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html
\* For example, the spec might have a constant Proc
\* whose value represents a set of processes.
\* You could just let a process be a number,
\* substituting an ordinary value like {1, 2, 3} for Proc.
\* However, a better way is to represent a process by a TLC model value.
\* A model value is an unspecified value that
\* TLC considers to be unequal to any value that you can express in TLA+.
\* You can substitute the set {p1, p2, p3} of three model values for Proc.
\* If by mistake you write an expression like p+1
\* where the value of p is a process,
\* TLC will report an error when it tries to evaluate that expression
\* because it knows that a process is a model value and thus not a number.
\* An important reason for substituting a set of model values for Proc is to
\* let TLC take advantage of symmetry.
PRIESTS = {p1, p2, p3}
DECREES = {d1, d2, d3}
BALLOT_IDS = {0, 1, 2}

SYMMETRY
SYMM

INIT
Init

NEXT
Next

INVARIANT
TypeOK
Consistent
```

```bash
export JAVA_OPTS="-Xms80g -XX:+UseParallelGC"
tlc SynodBasicProtocol.tla -config SynodBasicProtocol-WithSymmetrySets.cfg -deadlock -workers 40
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 1.3E-7
#   based on the actual fingerprints:  val = 1.3E-7
# 3663798 states generated, 809615 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 28.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 12 and the 95th percentile is 3).
# Finished in 31s at (2023-07-08 21:22:58)
```

+ According to the research paper [ResearchGate: The Investigation of TLC Model Checker Properties](https://www.researchgate.net/publication/304894406_The_Investigation_of_TLC_Model_Checker_Properties), there are two approaches for TLC method usage: the breadth-first search (BFS) of transition system states and the depth-first search (DFS). To optimize the search time, it is common to skip some states that have been searched before, such as:
  + Equal states: If the TLC model checker has encountered the state `xs == {x1, x2, x3}` before, it does not need to search it again.
  + Symmetry states: For example, if the TLC model checker has searched the state `xs == [x1 |-> 1, x2 |-> 2, x3 |-> 3]` and **all** subsequent expressions (e.g., `DOMAIN`) are symmetric for that state, then it does not need to search the symmetry state (e.g., `xs == [x3 |-> 1, x2 |-> 2, x1 |-> 1]`, by interchanging `x1` and `x3`).
    + Symmetry states are generated based on symmetry sets. However, the precise relationship between symmetry states and symmetry sets is unclear to me.
+ According to the guide [The Microsoft Research-Inria Joint Center: Model Values and Symmetry](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html), a set `S` of model values should be declared as a symmetry set only if **the specification and all properties** being checked are symmetric for `S` after the substitutions for constants and defined operators specified by the model are made.
  + An expression is symmetric for a set `S` if and only if interchanging any two values of `S` does not change the value of the expression. The expression `{{x1, x2}, {x1, x3}, {x2, x3}}` is symmetric for the set `{x1, x2, x3}` -- for example, interchanging `x1` and `x3` in this expression produces `{{x3, x2}, {x3, x1}, {x2, x1}}`, which is equal to the original expression.
  + According to [TLA+ Video Course](https://lamport.azurewebsites.net/video/video7-script.pdf), there are two criteria to determine if a set is a symmetry set:
    + It's OK to use elements of a symmetry set in an expression assigned to another constant if the expression is symmetric in the elements of the symmetry set. There's one additional condition for symmetry sets.
    + Elements of a symmetry set, or a constant assigned elements of a symmetry set may not appear in a `CHOOSE` expression.
  + I believe the reasons for these criteria are:
    + A set itself exhibits symmetry. For example, `{x1, x2, x3}` = `{x3, x2, x1}`.
    + Declaring a constant that is constructed from the set and whose value depends on the ordering of elements in the set can break the symmetry. For example, the constant `{{x1, x2}, {x2, x3}}` makes the set `{x1, x2, x3}` not symmetric. This is because interchanging `x1` and `x2` yields `{{x2, x1}, {x1, x3}}`, which is not equal to the original constant `{{x1, x2}, {x2, x3}}`.
    + According to the guide [The Microsoft Research-Inria Joint Center: Model Values and Symmetry](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html), the **only** TLA+ operator that can produce a non-symmetric expression when applied to a symmetric expression is `CHOOSE`. For example, the expression `CHOOSE x \in {x1, x2, x3}: TRUE` is not symmetric for `{x1, x2, x3}`.

## Ordinary Expressions

The content of this section is derived from [the video script](https://lamport.azurewebsites.net/video/video8a-script.pdf) for "The TLA+ Video Course, Lecture 8, Part 1" by Leslie Lamport.

A module-closed expression is a TLA+ expression that (after expanding definitions) contains only:

+ built-in TLA+ operators and constructs,
+ numbers and strings, like 42 and "abc",
+ declared constants and variables,
+ identifiers declared locally within it.
  + forall: `\A v \in S: ...`
  + exists: `\E v \in S: ...`
  + function constructor: `[v \in S |-> ...]`
  + set constructors: `{v \in S: ...}`, `{...: v \in S}`

`\E v \in Nat: x' = x + v` is module-complete if `x` is a declared variable. However, the subexpression `x' = x + v` is not module-complete because `v` is locally declared outside it.

A module-closed formula is a Boolean-valued module-closed expression. That is, one whose value is either `TRUE` or `FALSE`. For example, `(x \in 1..42) /\ (y' = x + 1)` - assuming x and y are declared variables.

+ A constant expression is a (module-complete) expression that (after expanding all definitions) does not contain declared variables nor non-constant operators. The only non-constant operators that we've seen so far are `'` and `UNCHANGED`.
  + The value of a constant expression depends only on the values of the declared constants it contains.
+ A state expression is a (module-complete) expression that can contain anything a constant expression can contain as well as variables declared in a `VARIABLES` statement. For example, `x + y[foo]` is a state expression, if `foo` is a declared constant and `x` and `y` are declared variables.
  + The value of a state expression depends on the values of declared constants and the values of declared variables. Let's ignore dependence on the values of declared constants.
  + Remember that a state assigns values to variables. Then, a state expression has a value on a state. For example, if state `s` assigns `v <- Nat` and `w <- -42`, then the state expression `v \union {w}` has the value `Nat \union {-42}`.
  + A constant expression is a state expression that has the same value on all states.
+ An action expression can contain anything a state expression can as well as `'` and `UNCHANGED`.
  + An action expression has a value on a step (pair of states). For example, if state `s` assigns `p <- 42` and state `t` assigns `q <- 24`, then the action expression `p - q'` has the value `42 - 24` on the step `s -> t`.
  + A state expression is an action expression whose value on the step `s-> t` depends only on the first state `s`.

## Temporal Formulas

The content of this section is derived from [the video script](https://lamport.azurewebsites.net/video/video8a-script.pdf) for "The TLA+ Video Course, Lecture 8, Part 1" by Leslie Lamport.

A temporal formula (TLA+ has only Boolean-valued temporal expressions – that is, temporal formulas) has a Boolean value on a behavior (A sequence of states is just what we've been calling a behavior) `s1 -> s2 -> s3 -> ...`. We can write a specification as a temporal formula – a formula whose value is `TRUE` on the behaviors allowed by the spec.

In general, the specification with initial formula `Init`, next-state formula `Next`, declared variables `v1, ..., vn` is expressed by the temporal formula `Init /\ [][Next]_<<v1, ..., vn>>`.

+ A state formula like `Init` is true on a behavior (`s1 -> s2 -> s3 -> s4 -> ...`) if and only if it's true on the first state (`s1`) of the behavior.
+ The temporal formula always `Next` (`[][Next]_<<v1, ..., vn>>`) is true on a behavior (`s1 -> s2 -> s3 -> s4 -> ...`) if and only if `Next` is true on every step of the behavior (`si -> s(i+1)` for all `i`).

```tla
Spec ==
  /\ Init
  /\ [][Next]_{<<priestStatus, ledgers, usedBallotIds, msgs>>}
```

```cfg
\* SynodBasicProtocol.cfg
CONSTANT
PRIESTS = {p1, p2, p3}
DECREES = {d1, d2, d3}
\* Even a modest increase in the range of BALLOT_IDS,
\* from 0..2 to 0..10,
\* can significantly increase the number of possible distinct states.
BALLOT_IDS = {0}

SPECIFICATION
Spec

INVARIANT
TypeOK
Consistent
```

```bash
tlc SynodBasicProtocol.tla -config SynodBasicProtocol.cfg -deadlock
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 3.9E-14
# 1822 states generated, 565 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 12.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 12 and the 95th percentile is 3).
# Finished in 02s at (2023-07-09 07:01:51)
```

Let's now see what it means to apply the Always operator to a state formula.

+ For the action `Next`, always `Next` is true on a behavior if and only if `Next` is true on every step of the behavior.
+ The state formula `TypeOK` is an action whose value on `si -> s(i+1)` **depends only on `si`** (a state formula is an action formula whose value on a step depends only on the first state of the step), so `[]TypeOK` is true on a behavior (`s1 -> s2 -> s3 -> s4 -> ...`) if and only if `TypeOK` is true on every **state** of the behavior (`si` for all `i`).
+ You can write `[]TypeOK`. You don't need the `[]_<<v1, ..., vn>>` for `[]StateFormula`.

## Stuttering Steps

The content of this section is derived from [the video script](https://lamport.azurewebsites.net/video/video8b-script.pdf) for "The TLA+ Video Course, Lecture 8, Part 2" by Leslie Lamport.

```tla+
--------------------------- MODULE SimpleProgram ---------------------------
\* SimpleProgram.tla
EXTENDS Integers
VARIABLES i, j

Init ==
  /\ i = 0
  /\ j = 0

IncrIJ ==
  \/ /\ i = 0
     /\ i' = 1
     /\ UNCHANGED <<j>>
  \/ /\ j = 0
     /\ j' = 1
     /\ UNCHANGED <<i>>

SimpleProgramSpec ==
  /\ Init
  /\ [][IncrIJ]_<<i, j>>
============================================================================
```

```tla+
--------------------------- MODULE SimpleProgramImpl -----------------------
\* SimpleProgramImpl.tla
EXTENDS Integers
VARIABLES i, j, k

Init ==
  /\ i = 0
  /\ j = 0
  /\ k = 0

IncrIJ ==
  \/ /\ i = 0
     /\ i' = 1
     /\ UNCHANGED <<j, k>>
  \/ /\ j = 0
     /\ j' = 1
     /\ UNCHANGED <<i, k>>

IncrK ==
  /\ k = 0
  /\ k' = 1
  /\ UNCHANGED <<i, j>>

IncrIJK ==
  \/ IncrIJ
  \/ IncrK

SimpleProgramImplSpec ==
  /\ Init
  /\ [][IncrIJK]_<<i, j, k>>

SP == INSTANCE SimpleProgram
SimpleProgramSpec == SP!SimpleProgramSpec
\* https://lamport.azurewebsites.net/video/video8b-script.pdf
\* 1. Asserts that for every behavior:
\*    if it satisfies SimpleProgramImplSpec, then it satisfies SimpleProgramSpec.
\* 2. Every behavior satisfying SimpleProgramImplSpec satisfies SimpleProgramSpec.
\* 3. SimpleProgramImplSpec implements SimpleProgramSpec.
THEOREM SimpleProgramImplSpec => SimpleProgramSpec
============================================================================
```

```cfg
\* SimpleProgramImpl.cfg
SPECIFICATION
SimpleProgramImplSpec

PROPERTY
\* THEOREM SimpleProgramImplSpec => SimpleProgramSpec
\* Let TLC check this theorem by adding SimpleProgramSpec
\* as a property to check
\* in a model you constructed for module SimpleProgramImpl.
SimpleProgramSpec
```

```bash
tlc SimpleProgramImpl.tla -config SimpleProgramImpl.cfg -deadlock
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = 2.2E-18
# 13 states generated, 8 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 4.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 3 and the 95th percentile is 3).
# Finished in 01s at (2023-07-12 01:48:18)
```

How can the theorem `SimpleProgramImplSpec => SimpleProgramSpec` make sense?

+ The theorem `SimpleProgramImplSpec => SimpleProgramSpec` may not make sense because `SimpleProgramSpec` and `SimpleProgramImplSpec` refer to different state spaces constructed from different variables.
  + `SimpleProgramSpec` is an assertion about behaviors whose states assign a value to the two variable `i` and `j`.
  + `SimpleProgramImplSpec` is an assertion about behaviors whose states assign values to the two variables `i`, `j` and `k`.
+ Viewing states as implicitly containing infinitely many variables representing the entire universe is a key insight for understanding why theorems like `SimpleProgramImplSpec => SimpleProgramSpec` may hold. A formula denotes constraints on the values of variables in a state, but a state itself implicitly contains infinitely many variables that represent the entire universe. Two formulas may involve different variables yet still be assertions over this same implicit infinite state space.
  + For instance, the formula `i = 0` constrains the value of `i` but says nothing about other variables like `k`, `Mozart`, or `numberOfCustomersInTimbuktuStarbucks` that **also exist** in the state.
  + Specifications are not programs; they're mathematical formulas. In math, when you write: `x + y = 7`, it doesn't mean that there's no variable `z` or `w`. The equations just say nothing about those other variables.
+ It's useful to think about specifications as follows.
  + A specification does not describe the correct behavior of a system.
  + Rather, it describes a universe in which the system **and its environment** are behaving correctly. The spec describes not only the system, but other parts of the universe that the system depends on.
  + The spec says nothing about irrelevant parts of the universe.

The theorem `SimpleProgramImplSpec => SimpleProgramSpec` makes sense because both formulas are assertions about the same kind of behavior. It asserts that every behavior satisfying `SimpleProgramImplSpec` satisfies `SimpleProgramSpec`. But how can it be true?

+ `SimpleProgramImplSpec` allows `IncrK` steps, which leave `i` and `j` unchanged. All `SimpleProgramSpec` steps change `i` or `j`. How can a behavior satisfying `SimpleProgramImplSpec` also satisfy `SimpleProgramSpec` if it has a `IncrK` step? How can the theorem be true?
+ It's the "magic" of `[]_<<i, j>>`. `[IncrIJ]_<<i, j>>` is true on a behavior iff `IncrIJ \/ UNCHANGED <<i, j>>` is true on every step of the behavior, which is the same as the assertion that every step satisfies `IncrIJ` or leaves `i` and `j` unchanged. If steps leaving `i` and `j` unchanged were not allowed by `SimpleProgramSpec`, then the theorem `SimpleProgramImplSpec => SimpleProgramSpec` would not be true.
+ Similarly, for the two-phase commit spec `TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>`, this always formula is true on a behavior if and only if every step of the behavior satisfies the next-state formula `TPNext` or else leaves **all** the specification variables unchanged.

However, we cannot remove the stuttering steps allowed by `[]_<<i, j>>` in TLA+, because if we write `SimpleProgramSpec == Init /\ [][Next]_<<>>`, then this will allow stuttering steps, as explained by Stephan Merz in [Google Groups: About stuttering steps, deadlock and Implementation](https://groups.google.com/g/tlaplus/c/Pg5Yx3k_VaE):

```tla
  [Next]_<<>>
= Next \/ UNCHANGED <<>> \* By definition of [Next]_vars.
= Next \/ (<<>>' = <<>>) \* By definition of UNCHANGED.
= Next \/ (<<>> = <<>>)  \* Since <<>> is a constant expression.
= Next \/ TRUE
```

Now, `TRUE` allows for any step, including stuttering transitions: there is **no way** you can write a TLA+ specification that **disallows** stuttering steps.

If we write `SimpleProgramSpec == Init /\ [][Next]_<<i>>`, then this will also allow stuttering steps:

```tla
  [Next]_<<i>>
= Next \/ UNCHANGED <<i>>  \* By definition of [Next]_vars.
= Next \/ (<<i>>' = <<i>>) \* By definition of UNCHANGED.
= Next \/ (<<i'>> = <<i>>) \* Since <<>> is a constant expression.
= Next \/ (i' = i)
```

Now, `i' = i` allows for any step that keep `i` unchanged, including stuttering transitions.

Steps that leave all the spec's variables unchanged are called stuttering steps. Every TLA+ spec allows them.

+ If they didn't, TPSpec would allow the value of `numberOfCustomersInTimbuktuStarbucks` to change only when the protocol took a step. And that would be really weird.
+ If they didn't, the two-phase commit spec would allow the value of every variable in the universe to change only when the two-phase commit protocol took a step. And that would be really weird.
+ But the most important reason to allow stuttering steps is embodied in this theorem: `SimpleProgramImplSpec => SimpleProgramSpec`. Implementation becomes simple logical implication.
  + Mathematical simplicity is not an end in itself.
  + It's a sign that we're doing things right.

We represent a terminating execution by a behavior ending in an infinite sequence of stuttering steps. This is natural, because a behavior represents a history of the universe, and the universe keeps going even if the system we're specifying terminates. It is important to note that termination and deadlock are distinct concepts, as Leslie Lamport explained in [Google Groups: Question about some concepts](https://groups.google.com/g/tlaplus/c/EfE9YrfqmBU): "Deadlock means reaching a state in which the only steps (state changes) allowed by the spec are stuttering steps (ones that change no declared variables of the spec)." Thus, a specification can reach a deadlock state even if stuttering steps are permitted.

## Weak Fairness & Strong Fairness

At this moment, I am finding it challenging to grasp the concepts of weak fairness and strong fairness, particularly as they relate to the formalization of fairness using the Linear Temporal Logic (LTL) operators `[]<>p` and `<>[]p`. These concepts require a deep understanding of LTL, which I am currently in the process of acquiring. Therefore, I have decided to temporarily skip this part of my studies. Once I have a more solid foundation in LTL, I will return to explore these topics in greater depth.

## Reference

+ [The TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
+ [Medium: Introduction to TLA+ Model Checking in the Command Line](https://medium.com/software-safety/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2)
+ [Learn TLA+](https://www.learntla.com/index.html)
+ [Auxiliary Variables in TLA+](https://lamport.azurewebsites.net/pubs/auxiliary.pdf)
+ [A. Jesse Jiryu Davis: Current and Future Tools for Interactive TLA+](https://emptysqua.re/blog/interactive-tla-plus/#is-the-spec-behaving-as-intended)
+ [Tautvidas Sipavičius: Debugging TLA+ specifications with state dumps](https://www.tautvidas.com/blog/2019/01/debugging-tla-specifications-with-state-dumps/)
+ [tlaplus/tlaplus Issues: Specifying symmetry set in cfg file manually](https://github.com/tlaplus/tlaplus/issues/404)
+ [The Microsoft Research-Inria Joint Center: Model Values and Symmetry](https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/model-values.html)
+ [ResearchGate: The Investigation of TLC Model Checker Properties](https://www.researchgate.net/publication/304894406_The_Investigation_of_TLC_Model_Checker_Properties)
+ [Google Groups: About stuttering steps, deadlock and Implementation](https://groups.google.com/g/tlaplus/c/Pg5Yx3k_VaE)
+ [Google Groups: About stuttering steps and deadlock in TLC](https://groups.google.com/g/tlaplus/c/WhgEGDTziBM)
+ [Google Groups: Question about some concepts](https://groups.google.com/g/tlaplus/c/EfE9YrfqmBU)
+ [HILLEL WAYNE: WEAK AND STRONG FAIRNESS](https://www.hillelwayne.com/post/fairness/)
