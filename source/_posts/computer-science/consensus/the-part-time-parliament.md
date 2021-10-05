---
layout: post
title: The Part-Time Parliament
date: 2022-10-05 12:00:00
categories:
  - [Computer Science, Consensus]
math: true
---

## Introduction

Honestly, it took me at least a year to develop a solid understanding of the Paxos consensus algorithm. As the authors of [Raft: In Search of an Understandable Consensus Algorithm](https://www.usenix.org/system/files/conference/atc14/atc14-paper-ongaro.pdf) wrote:

> We struggled with Paxos ourselves; we were not able to understand the complete protocol until after reading several simplified explanations and designing our own alternative protocol, a process that took almost a year.

## The Problem

### Requirements

+ The first requirement of the parliamentary protocol was the **consistency** of ledgers, meaning that no two ledgers could contain contradictory information. If legislator $\Phi \iota \sigma \partial \epsilon \rho$ had the entry 132: Lamps must use only olive oil, then no other legislator's ledger could have a different entry for decree 132.
+ Progress condition: If a **majority** of the legislators were in the Chamber and no one entered or left the Chamber for a **sufficiently long** period of time then any decree proposed by a legislator in the Chamber would be passed, and every decree that had been passed would appear in the ledger of every legislator in the Chamber.

### Assumptions

+ Each legislator received a **sturdy ledger** in which to record the decrees, a pen, and a supply of **indelible ink**.
+ A legislator would write other notes on a slip of **paper**, which he might (or might not) lose if he left the Chamber.
+ Achieving the progress condition required that legislators be able to measure the passage of time, so they were given simple hourglass **timers**.
+ A messenger could be counted on not to garble messages, but he might forget that he had already delivered a message, and **deliver it again**. A messenger might leave the Chamber to conduct some business—perhaps taking a six-month voyage—before delivering a message. He might even leave forever, in which case the message would **never be delivered**.

## The Single-Decree Synod

Let us consider a simple consensus algorithm named Synod, a precursor to the Parliament protocol. The protocol’s requirements and assumptions were essentially the same as those of the later Parliament except that instead of containing a sequence of decrees, a ledger would have at most one decree. The Synod targets priests, not legislators, as its users.

Mathematicians derived the Synod protocol in a series of steps:

+ First, they proved results showing that a protocol satisfying certain constraints would guarantee consistency and **allow** progress (not deadlock). A preliminary protocol was then derived directly from these constraints.
+ A restricted version of the preliminary protocol provided the basic protocol that guaranteed consistency, but **not progress**.
+ The complete Synod protocol, **satisfying the consistency and progress requirements**, was obtained by restricting the basic protocol.

### Mathematical Results

The Synod’s decree was chosen through a series of numbered **ballots**, where a ballot was a referendum on a single decree. Formally, a ballot $B$ consisted of the following four components:

+ $B_{dec}$: A decree (the one being voted on).
+ $B_{qrm}$: A nonempty set of priests (the ballot's quorum).
+ $B_{vot}$: A set of priests (the ones who cast votes for the decree).
+ $B_{bal}$: A ballot number.

A ballot succeeded iff (if and only if) **every** priest in the quorum voted for the decree. A ballot $B$ was said to be **successful** iff $$B_{qrm} \subseteq B_{vot}$, so a successful ballot was one in which every quorum member voted.

Paxon mathematicians defined three conditions on a set $\mathcal{B}$ of ballots, and then showed that consistency was guaranteed and progress was possible if the set of ballots that had taken place satisfied those conditions:

+ $\operatorname{B1}(\mathcal{B})$: Each ballot in $\mathcal{B}$ has a unique ballot number.
+ $\operatorname{B2}(\mathcal{B})$: The quorums of **any two** ballots in $\mathcal{B}$ have **at least one** priest in common.
+ $\operatorname{B3}(\mathcal{B})$: For every ballot $B$ in $\mathcal{B}$, if any priest in $B$'s quorum **voted in an earlier ballot** in $\mathcal{B}$, then the decree of $B$ equals the decree of the latest of those earlier ballots.
  + Ballot numbers were chosen from an unbounded ordered set of numbers. If $B_{bal}^{\prime} > B_{bal}$, then ballot $B_{bal}^{\prime}$ was said to be later than ballot $B$.
  + However, this indicated **nothing** about the order in which ballots were conducted; a later ballot could actually have taken place before an earlier one.

Let us illustrates condition $\operatorname{B3}(\mathcal{B})$ with a set $\mathcal{B}$ of five ballots for a Synod consisting of the five priests $\mathrm{A}, \mathrm{B}, \Gamma, \Delta, \mathrm{E}$. This set $\mathcal{B}$ contains five ballots. For each ballot and priest, I mark Q if the priest is in the quorum, and QV if the priest votes, since voting implies quorum membership.

| Ballot Number | Decree   | $\mathrm{A}$ | $\mathrm{B}$ | $\Gamma$ | $\Delta$ | $\mathrm{E}$ |
| :-            | :-:      | :-:          | :-:          | :-:      | :-:      | :-:          |
| 2             | $\alpha$ | Q            | Q            | Q        | QV       |              |
| 5             | $\beta$  | Q            | Q            | QV       |          | Q            |
| 14            | $\alpha$ |              | QV           |          | Q        | QV           |
| 27            | $\beta$  | QV           |              | QV       | QV       |              |
| 29            | $\beta$  |              | QV           | Q        | Q        |              |

+ Ballot number 2 is the earliest ballot, so the condition on that ballot is trivially true.
+ None of ballot 5's four quorum members **voted** in an earlier ballot, so the condition on ballot 5 is also trivially true.
+ The only member of ballot 14's quorum to vote in an earlier ballot is $\Delta$, who **voted** in ballot number 2, so the condition requires that ballot 14's decree must equal ballot 2's decree.
+ (This is a successful ballot.) The members of ballot 27's quorum are $\mathrm{A}$, $\Gamma$, and $\Delta$. Priest $\mathrm{A}$ did not vote in an earlier ballot, the only earlier ballot $\Gamma$ **voted** in was ballot 5, and the only earlier ballot $\Delta$ **voted** in was ballot 2. The **latest** of these two earlier ballots is ballot 5, so the condition requires that ballot 27's decree must equal ballot 5's decree.
+ The members of ballot 29's quorum are $\mathrm{B}$, $\Gamma$, and $\Delta$. The only earlier ballot that $\mathrm{B}$ voted in was number 14, priest $\Gamma$ voted in ballots 5 and 27, and $\Delta$ voted in ballots 2 and 27. The latest of these four earlier ballots is number 27, so the condition requires that ballot 29's decree must equal ballot 27's decree.

#### A Formal Statement of Three Conditions

To state $\operatorname{B1}(\mathcal{B})$ - $\operatorname{B3}(\mathcal{B})$ formally requires some more notation. A vote $v$ was defined to be a quantity consisting of three components: a priest $v_{pst}$, a ballot number $v_{bal}$, and a decree $v_{dec}$. It represents a vote cast by priest $v_{pst}$ for decree $v_{dec}$ in ballot number $v_{bal}$. The Paxons also defined null votes to be votes $v$ with $v_{bal} = -\infty$ and $v_{dec} = \text{BLANK}$, where $-\infty < b < \infty$ for any ballot number $b$, and $\text{BLANK}$ is not a decree. For any priest $p$, they defined $null_p$ to be the unique null vote $v$ with $v_{pst} = p$.

For any votes $v$ and $v^{\prime}$, if $v_{bal} < v_{bal}^{\prime}$ then $v < v^{\prime}$. It is not known how the relative order of $v$ and $v^{\prime}$ was defined if $v_{bal} = v_{bal}^{\prime}$.

For any set $\mathcal{B}$ of ballots, the set $\operatorname{Votes}(\mathcal{B})$ of votes in $\mathcal{B}$ was defined to consist of all votes $v$ such that $v_{pst} \in B_{vot}$, $v_{bal} = B_{bal}$, and $v_{dec} = B_{dec}$ for some $B \in \mathcal{B}$.

If $p$ is a priest and $b$ is either a ballot number or $\pm \infty$, then $\operatorname{MaxVote}(b, p, \mathcal{B})$ was defined to be the largest vote $v$ in $\operatorname{Votes}(\mathcal{B})$ cast by $p$ with $v_{bal} < b$, or to be $null_p$ if there was no such vote. Since $null_p$ is smaller than any real vote cast by $p$, this means that $\operatorname{MaxVote}(b, p, \mathcal{B})$ is the largest vote in the set:

$$
  \left\{
    v \in \operatorname{Votes}(\mathcal{B}):
      \left(v_{pst}=p\right)
    \wedge
      \left(v_{bal}<b\right)
  \right\}
\cup
  \left\{null_p\right\}
$$

Conditions $\operatorname{B1}(\mathcal{B})$ – $\operatorname{B3}(\mathcal{B})$ are stated formally as follows:

\begin{aligned}
&B1(\mathcal{B}) \triangleq
  \forall B, B^{\prime} \in \mathcal{B}:
    \left(B \neq B^{\prime}\right)
    \Rightarrow
    \left(B_{bal} \neq B_{bal}^{\prime}\right)   \\

&B2(\mathcal{B}) \triangleq
  \forall B, B^{\prime} \in \mathcal{B}:
    B_{qrm} \cap B_{qrm}^{\prime} \neq \emptyset \\

&B3(\mathcal{B}) \triangleq
  \forall B \in \mathcal{B}:
    \left(\operatorname{MaxVote}(B_{bal}, B_{qrm}, \mathcal{B})_{bal} \neq -\infty\right)
    \Rightarrow                                  \\
    &\quad\left(B_{dec}=\operatorname{MaxVote}(B_{bal}, B_{qrm}, \mathcal{B})_{dec}\right)
\end{aligned}

#### Lemma

To show that these conditions imply consistency, the Paxons first showed that $\operatorname{B1}(\mathcal{B})$ – $\operatorname{B3}(\mathcal{B})$ imply that, if a ballot $B$ in $\mathcal{B}$ is **successful**, then any later ballot in $\mathcal{B}$ is for the same decree as $B$. If $\operatorname{B1}(\mathcal{B})$, $\operatorname{B2}(\mathcal{B})$, and $\operatorname{B3}(\mathcal{B})$ hold, then:

$$
\forall B, B^{\prime} \in \mathcal{B}:
    \left(
        \left(B_{qrm} \subseteq B_{vot}\right)
      \wedge
        \left(B_{bal}^{\prime} > B_{bal}\right)
    \right)
  \Rightarrow
    \left(B_{dec}^{\prime} = B_{dec}\right)
$$

##### Proof of Lemma

The author uses $B_{qrm} \subseteq B_{vot}$ instead of $B_{qrm} = B_{vot}$ to express a successful ballot $B$. This is because $B_{qrm} = B_{vot}$ is logically equivalent to $\left(B_{vot} \subseteq B_{qrm}\right) \wedge \left(B_{qrm} \subseteq B_{vot}\right)$, but only the condition $B_{qrm} \subseteq B_{vot}$ is required to prove the lemma.

For any ballot $B$ in $\mathcal{B}$, let $\operatorname{\Psi}(B, \mathcal{B})$ be the set of ballots in $\mathcal{B}$ later than $B$ for a decree different from $B$'s:

$$
\operatorname{\Psi}(B, \mathcal{B}) \triangleq
    \left\{
      B^{\prime} \in \mathcal{B}:
          \left(B_{bal}^{\prime} > B_{bal}\right)
        \wedge
          \left(B_{dec}^{\prime} \neq B_{dec}\right)
    \right\}
$$

To prove the lemma, it suffices to show that if  $B_{qrm} \subseteq B_{vot}$ then $\operatorname{\Psi}(B, \mathcal{B})$ is empty. The Paxons gave a proof by contradiction. They assumed the existence of a $B$ with $B_{qrm} \subseteq B_{vot}$ and $\operatorname{\Psi}(B, \mathcal{B}) \neq \emptyset$, and obtained a contradiction as follows:

1. Choose $C \in \operatorname{\Psi}(B, \mathcal{B})$ such that $C_{bal} = \min \left\{B_{bal}^{\prime}: B^{\prime} \in \Psi(B, \mathcal{B})\right\}$. Proof:
   + $C$ exists because $\operatorname{\Psi}(B, \mathcal{B})$ is nonempty and finite.
2. $C_{bal} > B_{bal}$. Proof:
   + By the definition of $\operatorname{\Psi}(B, \mathcal{B})$ and 1.
3. $B_{vot} \cap C_{qrm} \neq \emptyset$. Proof:
   + Given ballot $B$ is successful, then $B_{qrm} \subseteq B_{vot}$ (by definition of a successful ballot).
   + By $\operatorname{B2}(\mathcal{B})$, $B_{qrm} \cap C_{qrm} \neq \emptyset$.
   + Therefore, $B_{vot} \cap C_{qrm} \neq \emptyset$.
4. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \geq B_{bal}$. Proof:
   + By definition, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$ is the largest vote in the set $\eqref{proof-of-lemma:step-4:by-definition}$.
   + There exists at least one vote $v$ by priest $p$ in ballot $B$ satisfying the following conditions:
     + By 2, $v_{bal} = B_{bal} < C_{bal}$.
     + By 3, $(p \in B_{vot}) \wedge (p \in C_{qrm})$.
     + Therefore, $v$ is a valid element of the set denoted by Equation $\eqref{proof-of-lemma:step-4:by-definition}$.
5. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B}) \in \operatorname{Votes}(\mathcal{B})$. Proof:
   + By 4, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$ is not a null vote.
   + By the definition of $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$.
6. $C_{dec} = \operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec}$. Proof:
   + By 5, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \neq -\infty$.
   + By $B3(\mathcal{B})$.
7. i.  $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec} \neq B_{dec}$. Proof:
       + By the definition of $\operatorname{\Psi}(B, \mathcal{B})$ and 1, $C_{dec} \neq B_{dec}$.
       + By 6, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec} \neq B_{dec}$.
   ii. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \neq B_{bal}$. Proof:
       + By $\left(B_{dec}^{\prime} \neq B_{dec}\right) \Rightarrow \left(B^{\prime} \neq B\right)$, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B}) \neq B$.
       + By $\operatorname{B1}(\mathcal{B})$, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \neq B_{bal}$.
8. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} > B_{bal}$. Proof:
   + By 4 and 7.ii.
9. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B}) \in \operatorname{Votes}(\Psi(B, \mathcal{B}))$. Proof:
   + By the definition of $\operatorname{\Psi}(B, \mathcal{B})$, 8 and 7.i.
10. $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} < C_{bal}$. Proof:
    + By definition of $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$.
11. Contradiction. Proof:
    + Ballot $C$ does not have the minimum ballot ID in the set $\operatorname{\Psi}(B, \mathcal{B})$.
      + By 8, $B_{bal} < \operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal}$.
      + By 10, $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} < C_{bal}$.
      + By 7.i., $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec} \neq B_{dec}$.
    + By 1.
    + By 9. Why do we need step 9 to prove the contradiction in this case?

\begin{align}
  \left\{
    v \in \operatorname{Votes}(\mathcal{B}):
      \left(v_{pst} \in C_{qrm}\right)
    \wedge
      \left(v_{bal} < C_{bal}\right)
  \right\}
\cup
  \left\{null_p\right\}
\label{proof-of-lemma:step-4:by-definition}
\end{align}

##### Understanding the Proof of the Lemma

The author proves the Lemma in the section "Proof of Lemma". I would like to analyze how the author constructed the proof in a new section. However, constructing the proof **from scratch** is too difficult. The key idea is that the author proves the Lemma by contradiction.

The contradiction is that we assume $C$ is the "first" ballot whose decree differs from $B_{dec}$ (step 1). However, we can find another ballot whose number is $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal}$ that occurs "between" $B$ and $C$ and satisfies the required condition (step 11).

+ $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec} \neq B_{dec}$ (step 7.i)
  + $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{dec} = C_{dec}$ (step 6)
    + $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$ is not a null vote (step 5)
      + $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \ge B_{bal}$ (step 4)
    + $\operatorname{B3}(\mathcal{B})$
+ $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \gt B_{bal}$ (step 8)
  + $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \ge B_{bal}$ (step 4)
    + At least one priest in the quorum $C_{qrm}$ has cast a vote for ballot $B$.
      + $B_{vot} \cap C_{qrm} \neq \emptyset$ (step 3)
      + $C_{bal} > B_{bal}$ (step 2)
    + By the definition of $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})$.
  + $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \neq B_{bal}$ (step 7.ii)
+ $\operatorname{MaxVote}(C_{bal}, C_{qrm}, \mathcal{B})_{bal} \lt C_{bal}$ (step 10)

#### Theorem 1

With this lemma, it was easy to show that, if $\operatorname{B1}(\mathcal{B})$ – $\operatorname{B3}(\mathcal{B})$ hold, then any two **successful** ballots are for the **same** decree.

$$
\forall B, B^{\prime} \in \mathcal{B}:
    \left(
        \left(B_{qrm} \subseteq B_{vot}\right)
      \wedge
        \left(B_{qrm}^{\prime} \subseteq B_{vot}^{\prime}\right)
    \right)
  \Rightarrow
    \left(B_{dec}^{\prime} = B_{dec}\right)
$$

##### Proof of Theorem 1

+ If $B_{bal}^{\prime} = B_{bal}$, then $\operatorname{B1}(\mathcal{B})$ implies $B^{\prime} = B$.
+ If $B_{bal}^{\prime} \neq B_{bal}$, then the theorem follows immediately from the lemma.

#### Theorem 2

The Paxons then proved a theorem asserting that if there are enough priests in the Chamber, then it is **possible** to conduct a successful ballot while preserving $\operatorname{B1}$ – $\operatorname{B3}$. Although this **does not guarantee progress**, it at least shows that a balloting protocol based on $\operatorname{B1}$ – $\operatorname{B3}$ **will not deadlock**.

Let $b$ be a ballot number and $Q$ a set of priests such that $b > B_{bal}$ and $Q \cap B_{qrm} \neq \emptyset$ for all $B \in \mathcal{B}$. If $\operatorname{B1}(\mathcal{B})$, $\operatorname{B2}(\mathcal{B})$, and $\operatorname{B3}(\mathcal{B})$ hold, then there **is** a ballot $B^{\prime}$ with $B_{bal}^{\prime} = b$ and $B_{qrm}^{\prime} = B_{vot}^{\prime} = Q$ such that $\operatorname{B1}(\mathcal{B} \cup \{B^\prime\})$, $\operatorname{B2}(\mathcal{B} \cup \{B^\prime\})$ and $\operatorname{B3}(\mathcal{B} \cup \{B^\prime\})$ hold.

+ Condition $\operatorname{B1}(\mathcal{B} \cup \{B^\prime\})$ follows from $\operatorname{B1}(\mathcal{B})$, the choice of $B_{bal}^{\prime}$, and the assumption about $b$.
+ Condition $\operatorname{B2}(\mathcal{B} \cup \{B^\prime\})$ follows from $\operatorname{B2}(\mathcal{B})$, the choice of $B_{qrm}^{\prime}$ , and the assumption about $Q$.
+ If $\operatorname{MaxVote}(b, Q, \mathcal{B})_{bal} = −\infty$ then let $B_{dec}^{\prime}$ be any decree, else **let it equal** $\operatorname{MaxVote}(b, Q, \mathcal{B})_{dec}$. Condition $\operatorname{B3}(\mathcal{B} \cup \{B^\prime\})$ then follows from $\operatorname{B3}(\mathcal{B})$.

### The Preliminary Protocol

The definition of the protocol specified how the set $\mathcal{B}$ changed, but the set was never explicitly calculated. The Paxons referred to $\mathcal{B}$ as a quantity observed only by the gods, since it might never be known to any mortal.

+ To maintain $\operatorname{B1}(\mathcal{B})$, each ballot had to receive a unique number. An obvious method would have been to let a ballot number be a pair consisting of an integer and a priest, using a lexicographical ordering, where $(13, \Gamma \rho \alpha \breve{\iota}) < (13, \Lambda \iota \nu \sigma \epsilon \breve{\iota}) < (15, \Gamma \rho \alpha \breve{\imath})$.
+ To maintain $\operatorname{B2}(\mathcal{B})$, a ballot's quorum was chosen to contain a $\mu \alpha \delta \zeta \partial \omega \rho \iota \tau \breve{\sigma} \sigma \tau$ of priests.
  + Initially, $\mu \alpha \delta \zeta \partial \omega \rho \iota \tau \breve{\sigma} \sigma \tau$ just meant a simple majority.
  + Later, it was observed that fat priests were less mobile and spent more time in the Chamber than thin ones, so a $\mu \alpha \delta \zeta \partial \omega \rho \iota \tau \breve{\sigma} \sigma \tau$ was taken to mean any set of priests whose total weight was more than half the total weight of all priests, rather than a simple majority of the priests.
  + When a group of thin priests complained that this was unfair, actual weights were replaced with symbolic weights based on a priest’s attendance record.
+ To maintain $\operatorname{B3}(\mathcal{B})$, before initiating a new ballot with ballot number $b$ and quorum $Q$, a priest $p$ had to find $\operatorname{MaxVote}(b, Q, \mathcal{B})_{dec}$. To do this, $p$ had to find $\operatorname{MaxVote}(b, q, \mathcal{B})$ for **each** priest $q$ in $Q$.
  + Priest $p$ obtains $\operatorname{MaxVote}(b, q, \mathcal{B})$ from $q$ by an **exchange of messages**.
  + Therefore, the first two steps in the protocol for conducting a single ballot initiated by $p$ are:
    + \(1\) Priest $p$ chooses a new ballot number $b$ and sends a $\operatorname{NextBallot}(b)$ message to **some** set of priests.
    + \(2\) A priest $q$ responds to the receipt of a $\operatorname{NextBallot}(b)$ message by sending a $\operatorname{LastVote}(b, v)$ message to $p$, where $v$ is the vote with the largest ballot number less than $b$ that $q$ has cast, or his null vote $null_q$ if $q$ did not vote in any ballot numbered less than $b$.
    + When $q$ sends the $\operatorname{LastVote}(b, v)$ message, $v$ equals $\operatorname{MaxVote}(b, q, \mathcal{B})$. But the set $\mathcal{B}$ of ballots changes as new ballots are initiated and votes are cast. To keep $\operatorname{MaxVote}(b, q, \mathcal{B})$ from changing, $q$ **must cast no new votes** with ballot numbers between $v_{bal}$ and $b$.

The next two steps in the balloting protocol (begun in step 1 by priest $p$) are:

+ \(3\) After receiving a $\operatorname{LastVote}(b, v)$ message from every priest in some **majority** set $Q$, priest $p$ initiates a new ballot with number $b$, quorum $Q$, and decree $d$, where $d$ is chosen to satisfy $\operatorname{B3}(\mathcal{B})$. He then records the ballot in the back of his ledger and sends a $\operatorname{BeginBallot}(b, d)$ message to **every** priest in $Q$.
  + The execution of step (3) is considered to add a ballot $B$ to $\mathcal{B}$, where $B_{bal} = b$, $B_{qrm} = Q$, $B_{vot} = \emptyset$ (no one has yet voted in this ballot), and $B_{dec} = d$.
  + In step (4), if priest $q$ decides to vote in the ballot, then executing that step is considered to change the set $\mathcal{B}$ of ballots by adding $q$ to the set $B_{vot}$ of voters in the ballot $B \in \mathcal{B}$.
+ \(4\) Upon receipt of the $\operatorname{BeginBallot}(b, d)$ message, priest $q$ decides whether or not to cast his vote in ballot number $b$.
  + He may not cast the vote if doing so would violate a promise implied by a $\operatorname{LastVote}(b^{\prime}, v^{\prime})$ message he has sent for some other ballot.
  + A priest has the option not to vote in step (4), even if casting a vote would not violate any previous promise.
  + If $q$ decides to vote for ballot number $b$, then he sends a $\operatorname{Voted}(b, q)$ message to $p$ and records the vote in the back of his ledger.

Steps (1) – (4) describe the complete protocol for initiating a ballot and voting on it. All that remains is to determine the results of the balloting and announce when a decree has been selected. Recall that a ballot is successful iff **every** priest in the quorum has voted.

+ \(5\) If $p$ has received a $\operatorname{Voted}(b, q)$ message from **every** priest $q$ in $Q$ (the quorum for ballot number $b$), then he writes $d$ (the decree of that ballot) in his ledger and sends a $\operatorname{Success}(d)$ message to every priest.
+ \(6\) Upon receiving a $\operatorname{Success}(d)$ message, a priest enters decree $d$ in his ledger.

Since a priest enters a decree in his ledger only if it is the decree of a successful ballot, Theorem 1 implies that the priests' ledgers are consistent.

+ The protocol does not address the question of progress. All the steps in this protocol are optional. For example, a priest $q$ can ignore a $\operatorname{NextBallot}(b)$ message instead of executing step (2). Failure to take an action can prevent progress, but it cannot cause any inconsistency because it cannot make $\operatorname{B1}(\mathcal{B})$ – $\operatorname{B3}(\mathcal{B})$ false.
+ Receiving multiple copies of a message can cause an action to be repeated.
  + Except in step (3), performing the action a second time has no effect. For example, sending several $\operatorname{Voted}(b, q)$ messages in step (4) has the same effect as sending just one.
  + By executing step (3) more than once, priest $p$ may initiate multiple ballots with the same ballot number $b$ but with different quorums $Q$, $Q'$, ... and decrees $d$, $d'$, ... The repetition of step (3) is prevented by using the entry made in the back of the ledger when it is executed.
  + Thus, the consistency condition is maintained even if a messenger delivers the same message several times.

### The Basic Protocol

One problem with the preliminary protocol was that keeping track of all this information would have been difficult for the busy priests. The Paxons therefore **restricted** the preliminary protocol to obtain the more practical basic protocol in which each priest $p$ had to maintain only the following information in the back of his ledger:

+ $\operatorname{lastTried}(p)$: The number of the last ballot that $p$ tried to initiate, or $-\infty$ if there was none.
  + Though the author does not explicitly state this, I believe the intent of introducing $\operatorname{lastTried}(p)$ is to prevent executing step (3) more than once, which would result in initiating multiple ballots with the same ballot number $b$ but with different quorums $Q$, $Q'$ and decrees $d$, $d'$.
  + The preliminary protocol allows $p$ to conduct any number of ballots concurrently. In the basic protocol, he conducts only one ballot at a time — ballot number $\operatorname{lastTried}(p)$. After $p$ initiates this ballot, he ignores messages that pertain to any other ballot that he had previously initiated.
  + Priest $p$ keeps all information about the progress of ballot number $\operatorname{lastTried}(p)$ on a slip of **paper**. If he loses that slip of paper, then he stops conducting the ballot.
+ $\operatorname{prevVote}(p)$: The **vote** cast by $p$ in the **highest**-numbered ballot in which he voted, or $-\infty$ if he never voted.
  + Upon receipt of a $\operatorname{NextBallot}(b)$ message from $q$ with $(b > \operatorname{prevVote}(p)_{bal}) \wedge (b > \operatorname{nextBal}(p))$, priest $p$ sends a $\operatorname{LastVote}(b, v)$ message to $q$, where $v$ equals $\operatorname{prevVote}(p)$.
  + If $b \le \operatorname{prevVote}(p)_{bal}$, then priest $p$ does not remember the vote with the largest ballot number less than $b$ that he has cast. Therefore, priest $p$ cannot respond.
  + If $b \le \operatorname{nextBal}(p)$, then priest $p$ will not vote due to his promise. Therefore, it is meaningless for priest $p$ to respond with a $\operatorname{LastVote}(b, v)$ message.
  + Before priest $p$ votes for ballot $b$ and updates $\operatorname{preVote}(p)$ to $b$, priest $p$ must have sent a $\operatorname{LastVote}(b, v)$ message to priest $q$ and updated $\operatorname{nextBal}(p)$ to $b$. Therefore, we have $\operatorname{nextBal}(p) \ge \operatorname{preVote}(p)$.
  + By $\eqref{the-basic-protocol:prev-vote}$, the following statements by the author make sense:
    + Upon receipt of a $\operatorname{NextBallot}(b)$ message from $q$ with $b > \operatorname{nextBal}(p)$, priest $p$ sets $\operatorname{nextBal}(p)$ to $b$ and sends a $\operatorname{LastVote}(b, v)$ message to $q$, where $v$ equals $\operatorname{prevVote}(p)$.
    + A $\operatorname{NextBallot}(b)$ message is ignored if $b \le \operatorname{nextBal}(p)$.
+ $\operatorname{nextBal}(p)$: The largest value of $b$ for which $p$ has sent a $\operatorname{LastVote}(b, v)$ message, or $-\infty$ if he has never sent such a message.
  + In the preliminary protocol, each $\operatorname{LastVote}(b, v)$ message sent by a priest $q$ represents a promise not to vote in any ballot numbered between $v_{bal}$ and $b$.
  + In the basic protocol, it represents the **stronger** promise not to cast a new vote in any ballot numbered less than $b$.

\begin{align}
\label{the-basic-protocol:prev-vote}
    &\quad\quad\left(
        \left(
            \left(b > \operatorname{prevVote}(p)_{bal}\right)
          \wedge
            \left(b > \operatorname{nextBal}(p)\right)
        \right) \nonumber
      \right.             \\
      &\quad\left.
      \wedge
        \left(
          \operatorname{nextBal}(p) \ge \operatorname{preVote}(p)
        \right)
    \right)     \nonumber \\
  &\Rightarrow
    \left(
      b > \operatorname{nextBal}(p)
    \right)
\end{align}

Steps 1–6 of the preliminary protocol become the following six steps for conducting a ballot in the basic protocol:

1. Priest $p$ chooses a new ballot number $b$ greater than $\operatorname{lastTried}(p)$,sets $\operatorname{lastTried}(p)$ to $b$, and sends a $\operatorname{NextBallot}(b)$ message to some set of priests. Please notice that the quorum $Q$ has not yet been determined.
2. Upon receipt of a $\operatorname{NextBallot}(b)$ message from $p$ with $b > \operatorname{nextBal}(q)$, priest $q$ sets $\operatorname{nextBal}(q)$ to $b$ and sends a $\operatorname{LastVote}(b, v)$ message to $p$, where $v$ equals $\operatorname{prevVote}(q)$. A $\operatorname{NextBallot}(b)$ message is ignored if $b \le \operatorname{nextBal}(q)$.
3. After receiving a $\operatorname{LastVote}(b, v)$ message from every priest in **some majority set** $Q$, where $b = \operatorname{lastTried}(p)$, priest $p$ initiates a new ballot with number $b$, quorum $Q$, and decree $d$, where $d$ is chosen to satisfy $\operatorname{B3}$. He then sends a $\operatorname{BeginBallot}(b, d)$ message to **every** priest in $Q$. (If $b \neq \operatorname{lastTried}(p)$, the $\operatorname{LastVote}(b, v)$ message is a response to a **previous** $\operatorname{NextBallot}(b)$ conducted by priest $p$; so, priest $p$ just ignores it.)
4. Upon receipt of a $\operatorname{BeginBallot}(b, d)$ message with $b = \operatorname{nextBal}(q)$, priest $q$ casts his vote in ballot number $b$, sets $\operatorname{prevVote}(q)$ to this vote, and sends a $\operatorname{Voted}(b, q)$ message to $p$. (A $\operatorname{BeginBallot}(b, d)$ message is ignored if $b \neq \operatorname{nextBal}(q)$.)
   1. We first prove that $\operatorname{nextBal}(q)$ is greater than or equal to the ballot number $b$ in the $\operatorname{BeginBallot}(b, d)$ message from priest $p$ to priest $q$. The proof is as follows: If priest $p$ sends an $\operatorname{BeginBallot}(b, d)$ message to priest $q$, it means priest $p$ has received an $\operatorname{LastVote}(b, v)$ message from priest $q$ and chosen priest $q$ as a member of the majority quorum set $Q$. Then, priest $q$ must have set $\operatorname{nextBal}(q)$ to $b$. In addition, we already know $\operatorname{nextBal}(q)$ increases monotonically. Therefore, we can conclude that $\operatorname{nextBal}(q)$ is greater than or equal to the ballot number $b$ in the $\operatorname{BeginBallot}(b, d)$ message from priest $p$ to priest $q$.
   2. Then, we can say $b \neq \operatorname{nextBal}(q)$ if and only if $b < \operatorname{nextBal}(q)$. By the requirement that $\operatorname{nextBal}(q)$ represents that priest $q$ cannot cast a new vote in any ballot numbered less than $\operatorname{nextBal}(q)$, priest $q$ should not cast a vote. In conclusion, priest $q$ ignores an $\operatorname{BeginBallot}(b, d)$ message with $b \neq \operatorname{nextBal}(q)$.
5. If $p$ has received a $\operatorname{Voted}(b, q)$ message from **every** priest $q$ in $Q$ (the quorum for ballot number $b$), where $b = \operatorname{lastTried}(p)$, then he writes $d$ (the decree of that ballot) in his ledger and sends a $\operatorname{Success}(d)$ message to **every** priest.
   1. We first prove that $\operatorname{lastTried}(p)$ is greater than or equal to the ballot number $b$ in the $\operatorname{Voted}(b, q)$ message. This is because priest $p$ sets $\operatorname{lastTried}(p)$ to a new ballot number $b^{\prime}$ before performing all the following steps.
   2. Then, we can say $b \neq \operatorname{lastTried}(p)$ if and only if $b < \operatorname{lastTried}(p)$, where $b$ comes from the $\operatorname{Voted}(b, q)$ message. Though the author does not explicitly state this, I believe that when priest $p$ initiates a new ballot, all information about the progress of the old ballot (e.g., quorum $Q$) on a slip of paper is forgotten. So, $\operatorname{Voted}(b, q)$ messages where $b < \operatorname{lastTried}(p)$ are ignored by priest $p$.
6. Upon receiving a $\operatorname{Success}(d)$ message, a priest enters decree $d$ in his ledger.

#### Proof of Consistency of the Basic Synodic Protocol

### The Complete Synod Protocol

To help achieve progress, the complete protocol includes the obvious additional requirement that priests perform steps 2–6 of the protocol as soon as possible. The key to the complete protocol lay in determining **when** a priest should initiate a ballot. Achieving the progress condition requires that new ballots be initiated until one succeeds, but that they not be initiated too frequently.

+ Never initiating a ballot will certainly prevent progress.
+ However, initiating too may ballots can also prevent progress. This can be best illustrated with a potential livelock scenario:
  + Priest $p1$ executes step 1, sends out $\operatorname{NextBallot}(b1)$ msgs to other priests.
  + Priest $p2$ executes step 1, sends out $\operatorname{NextBallot}(b2)$ msgs to other priests, and $b2 > b1$.
  + Priests which received $\operatorname{NextBallot}(b2)$ msgs cannot vote for $b1$ anymore. So $b1$ fails.
  + Priest $p1$ xecutes step 1 again, but with a larger ballot ID.

#### Liveness: T + 99min

The preceding sections have discussed the safety aspects of the Synod protocol. This section, however, delves into its liveness. Liveness, in the context of the Synod protocol, signifies that under certain conditions, the protocol can execute to completion within a finite timeframe.

By extending the protocol to require that if a priest $q$ received a $\operatorname{NextBallot}(b)$ or a $\operatorname{BeginBallot}(b, d)$ message from $p$ with $b < \operatorname{nextBal}(q)$, then he sent $p$ a message containing $\operatorname{nextBal}(q)$. Priest $p$ would then initiate a new ballot with a larger ballot number.

Let's assume that the following condition is met starting from time T:

+ A messenger who did not leave the Chamber would always deliver a message within 4 minutes, and a priest who remained in the Chamber would always perform an action within 7 minutes of the event that caused the action.
+ No priest or message exits.
+ $p$ is the only priest initiating ballots.

| Time    | Event                                                                       |
| :-      | :-                                                                          |
| T       | $p$ starts executing step 1.                                                |
| T + 7m  | $p$ sends a $\operatorname{NextBallot}(b1)$ message to some set of priests. |
| T + 11m | $q$ receives a $\operatorname{NextBallot}(b1)$ message from $p$.            |
| T + 18m | $q$ sends a $\operatorname{LastVote}(b1, v)$ message to $p$.                |
| T + 22m | $p$ receives a $\operatorname{LastVote}(b1, v)$ message from $q$.           |
| T + 29m | $p$ sends a $\operatorname{BeginBallot}(b1, d)$ message to $q$.             |
| T + 33m | $q$ receives a $\operatorname{BeginBallot}(b1, d)$ message from $p$.        |
| T + 40m | $q$ sends a message containing $\operatorname{nextBal}(q)$ to $p$.          |
| T + 44m | $p$ receives a message containing $\operatorname{nextBal}(q)$ from $q$.     |
| T + 51m | $q$ initiates a new ballot with a larger ballot number $b2$.                |
|         | $p$ sends a $\operatorname{NextBallot}(b2)$ message.                        |
| T + 55m | $q$ receives a $\operatorname{NextBallot}(b2)$ message from $p$.            |
| T + 62m | $q$ sends a $\operatorname{LastVote}(b2, v)$ message to $p$.                |
| T + 66m | $p$ receives a $\operatorname{LastVote}(b2, v)$ message from $q$.           |
| T + 73m | $p$ sends a $\operatorname{BeginBallot}(b2, d)$ message to $q$.             |
| T + 77m | $q$ receives a $\operatorname{BeginBallot}(b2, d)$ message from $p$.        |
| T + 84m | $q$ sends a $\operatorname{Voted}(b2, q)$ message to $p$.                   |
| T + 88m | $p$ receives a $\operatorname{Voted}(b2, q)$ message from $q$.              |
| T + 95m | $p$ writes $d$ in his ledger.                                               |
|         | $p$ sends a $\operatorname{Success}(d)$ message to every priest.            |
| T + 99m | $q$ receives a $\operatorname{Success}(d)$ message.                         |

#### Presidential Selection Requirement

Presidential selection requirement: If no one entered or left the Chamber, then after T minutes exactly one priest in the Chamber would consider himself to be the president.

The Paxons chose as president the priest whose name was last in alphabetical order among the names of all priests in the Chamber, though we don't know exactly how this was done. The presidential selection requirement would have been satisfied if a priest in the Chamber sent a message containing his name to every other priest at least once every T − 11 minutes, and a priest considered himself to be president iff he received no message from a "higher-named" priest for T minutes.

## The Multi-Decree Parliament

Logically, the parliamentary protocol used a separate instance of the complete Synod protocol for each decree number. This raises two questions:

+ What criteria should be used to determine the unique number for every Synod instance?
  + The number are assigned in a monotonically increasing order, incrementing by one with each new instance.
  + When a priest is selected as president, he carries out the first two steps of the Synod protocol for all instances.
  + Subsequently, he chooses the decree with the lowest number that he is still free to choose, and he performs step 3 for that decree number (instance of the Synod protocol) to try to pass the decree.
+ How to to establish the sequence of various Synod instances?
  + For further details, please refer to the 'Ordering of Decrees' section.

### The Protocol

The following modifications to this simple protocol lead to the actual Paxon Parliament’s protocol:

+ A single president was selected for all these instances, and he performed the first two steps of the protocol just once. The key to deriving the parliamentary protocol is the observation that, in the Synod protocol, the president does not choose the decree or the quorum until step 3. A newly elected president $p$ can send to some set of legislators a single message that serves as the $\operatorname{NextBallot}(b)$ message for all instances of the Synod protocol. (There are an infinite number of instances - one for each decree number.) A legislator $q$ can reply with a single message that serves as the $\operatorname{LastVote}$ messages for step 2 of all instances of the Synod protocol. This message contains only a finite amount of information, since $q$ can have voted in only a finite number of instances.
+ There is no reason to go through the Synod protocol for a decree number whose outcome is already known. Therefore, if a newly elected president $p$ has all decrees with numbers less than or equal to $n$ written in his ledger, then he sends a $\operatorname{NextBallot}(b, n)$ message that serves as a $\operatorname{NextBallot}(b)$ message in all instances of the Synod protocol for decree numbers larger than $n$. In his response to this message, legislator $q$ informs $p$ of all decrees numbered greater than $n$ that already appear in $q$'s ledger (in addition to sending the usual $\operatorname{LastVote}$ information for decrees not in his ledger), and he asks $p$ to send him any decrees numbered $n$ or less that are not in his ledger.
+ Suppose decrees 125 and 126 are introduced late Friday afternoon, decree 126 is passed and is written in one or two ledgers, but before anything else happens, the legislators all go home for the weekend. Suppose also that the following Monday, $\Delta \phi \omega \rho \kappa$ is elected the new president and learns about decree 126, but she has no knowledge of decree 125 because the previous president and all legislators who had voted for it are still out of the Chamber. She will hold a ballot that passes decree 126, which leaves a gap in the ledgers. Assigning number 125 to a new decree would cause it to appear earlier in the ledger than decree 126, which had been passed the previous week. Passing decrees out of order in this way might cause confusion - for example, if the citizen who proposed the new decree did so because he knew decree 126 had already passed. Instead, $\Delta \phi \omega \rho \kappa$ would attempt to pass a traditional decree that made absolutely no difference to anyone in Paxos. In general, a new president would fill any gaps in his ledger by passing the "olive-day" decree (The ides of February is national olive day).

You can find the specification in my other post [Implementing Multi-Decree Parliament In TLA+](https://clcanny.github.io/2023/07/24/computer-science/programming-language/tla+/implementing-multi-decree-parliament-in-tla/).

### Properties of the Protocol

#### The Ordering of Decrees

Balloting could take place concurrently for many different decree numbers, with ballots initiated by different legislators - each thinking he was president when he initiated the ballot. We cannot say precisely in what order decrees would be passed, especially without knowing how a president was selected.

+ A decree was said to to be proposed when it was chosen by the president in **step 3** of the corresponding instance of the Synod protocol.
+ The decree was said to be **passed** when it was written for the **first time** in a ledger.

If decrees $A$ and $B$ are important and decree $A$ was passed before decree $B$ was proposed, then $A$ has a lower decree number than $B$.

+ Before a president could propose any new decrees, he had to learn from all the members of a majority set what decrees they had voted for.
+ Any decree that had already been passed must have been voted for by at least one legislator in the majority set.
+ Therefore, the president must have learned about all previously passed decrees before initiating any new decree.
+ The president would not fill a gap in the ledgers with an important decree—that is, with any decree other than the "olive-day" decree.
+ He would also not propose decrees out of order.

#### Behind Closed Doors

### Further Developments

#### Picking a President

#### Long Ledgers

#### Bureaucrats

As Paxos prospered, legislators became very busy. Parlia- ment could no longer handle all details of government, so a bureaucracy was established.

+ To prevent such confusion, the Paxons had to guarantee that a position could be held by at most one bureaucrat at any time. To do this, a president included as part of each decree the time and date when it was proposed.
+ A bureaucrat was appointed for a short term, so he could be replaced quickly — for example, if he left the island. Parliament would pass a decree to extend the bureaucrat's term if he was doing a satisfactory job.
+ The following out-of-order proposal times are easily prevented because the parliamentary protocol satisfies this property: If two decrees are passed by different presidents, then one of the presidents proposed his decree after learning that the other decree had been proposed.

2854: 9:45 9 Apr 78 - $\Phi \rho \alpha \nu \sigma \epsilon \zeta$ is wine taster for 2 months.

2855: 9:20 9 Apr 78 - $\Pi \nu v \epsilon \lambda \breve{l}$ is wine taster for 1 month.

#### Learning the Law

Monotonicity condition: If one inquiry precedes a second inquiry, then the second inquiry cannot reveal an earlier state of the law than the first.

Initially, the monotonicity condition was achieved by passing a decree for each inquiry. If $\Sigma \partial \nu \breve{\iota} \delta \epsilon \rho$ wanted to know the current tax on olives, he would get Parlia- ment to pass a decree such as "87: Citizen $\Sigma \partial \nu \breve{\iota} \delta \epsilon \rho$ is reading the law". He would then read any ledger complete at least through decree 86 to learn the olive tax as of that decree. If citizen $\Gamma \rho \epsilon \epsilon \varsigma$ then inquired about the olive tax, the decree for his inquiry was proposed after decree 87 was passed, so the decree-ordering property implies that it received a decree number greater than 87.

#### Dishonest Legislators and Honest Mistakes

#### Choosing New Legislators

## Reference

+ [The Part-Time Parliament](https://www.microsoft.com/en-us/research/uploads/prod/2016/12/The-Part-Time-Parliament.pdf)
+ [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)
+ [Fast Paxos](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf)
+ [The Paxos Algorithm or How to Win a Turing Award](https://lamport.azurewebsites.net/tla/paxos-algorithm.html)
+ [Implementing Multi-Decree Parliament In TLA+](https://clcanny.github.io/2023/07/24/computer-science/programming-language/tla+/implementing-multi-decree-parliament-in-tla/)
+ [In Search of an Understandable Consensus Algorithm](https://www.usenix.org/system/files/conference/atc14/atc14-paper-ongaro.pdf)
+ [matklad: Notes on Paxos](https://matklad.github.io/2020/11/01/notes-on-paxos.html)
