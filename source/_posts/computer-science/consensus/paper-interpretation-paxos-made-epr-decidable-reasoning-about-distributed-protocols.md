---
layout: post
title: >-
  Paper Interpretation - Paxos Made EPR:
  Decidable Reasoning about Distributed Protocols
date: 2023-07-28 22:07:08
categories:
  - [Computer Science, Consensus]
math: true
---

https://arxiv.org/pdf/1710.07191.pdf

# Concepts

## EPR

[Wikipedia: Bernays–Schönfinkel class](https://en.wikipedia.org/wiki/Bernays%E2%80%93Sch%C3%B6nfinkel_class)

The Bernays-Schönfinkel class of formulas is a fragment of first-order logic formulas where satisfiability is decidable. It is the set of sentences that, when written in prenex normal form, have an $\exists^* \forall^*$ quantifier prefix and do not contain any function symbols. This class of logic formulas is also sometimes referred as effectively propositional (EPR) since it can be effectively translated into propositional logic formulas by a process of grounding or instantiation.

## Prenex Normal Form

[Wikipedia: Prenex normal form](https://en.wikipedia.org/wiki/Prenex_normal_form)

A formula of the predicate calculus is in prenex normal form (PNF) if it is written as a string of quantifiers and bound variables, called the prefix, followed by a **quantifier-free part**, called the **matrix**. Together with the normal forms in propositional logic (e.g. disjunctive normal form or conjunctive normal form), it provides a canonical normal form useful in automated theorem proving.
Every formula in classical logic is logically equivalent to a formula in prenex normal form. For example, if $\phi(y), \psi(z)$, and $\rho(x)$ are quantifier-free formulas with the free variables shown then $\forall x \exists y \forall z (\phi(y) \lor (\psi(z) \rightarrow \rho(x)))$ is in prenex normal form with matrix $\phi(y) \lor (\psi(z) \rightarrow \rho(x))$, while $\forall x((\exists y \phi(y)) \lor ((\exists z \psi(z)) \rightarrow \rho(x)))$ is logically equivalent but not in prenex normal form.

## Function Symbol

[Wikipedia: Functional predicate](https://en.wikipedia.org/wiki/Functional_predicate)

In formal logic and related branches of mathematics, a functional predicate, or function symbol, is a logical symbol that may be applied to an object term to produce another object term. Specifically, the symbol $F$ in a formal language is a functional symbol if, given any symbol $X$ representing an object in the language, $F(X)$ is again a symbol representing an object in that language. In typed logic, $F$ is a functional symbol with domain type $T$ and codomain type $U$ if, given any symbol $X$ representing an object of type $T$, $F(X)$ is a symbol representing an object of type $U$. One can similarly define function symbols of more than one variable, analogous to functions of more than one variable; a function symbol in zero variables is simply a constant symbol.

## Stratified Function Symbols

## Relation Symbol

[Wikipedia: First-order logic, Non-logical symbols](https://en.wikipedia.org/wiki/First-order_logic#:~:text=A%20predicate%20symbol%20(or%20relation,%22x%20is%20a%20man%22.)

A predicate symbol (or relation symbol) with some valence (or arity, number of arguments) greater than or equal to 0. These are often denoted by uppercase letters such as $P$, $Q$ and $R$. Examples:

+ In $P(x)$, $P$ is a predicate symbol of valence 1. One possible interpretation is "x is a man".
+ In $Q(x,y)$, $Q$ is a predicate symbol of valence 2. Possible interpretations include "x is greater than y" and "x is the father of y".
+ Relations of valence 0 can be identified with propositional variables, which can stand for any statement. One possible interpretation of $R$ is "Socrates is a man".

## Closed First-order Formulas

In logic, a formula is said to be "closed" if it has no free variables. A free variable is one that is not bound by a quantifier (either existential $\exists$ or universal $\forall$). For example, consider the following two formulas:

+ $P(x)$: In this formula, $x$ is a free variable because it's not bound by any quantifiers. Therefore, $P(x)$ is not a closed formula.
+ $\forall x P(x)$: In this formula, the variable $x$ is bound by the universal quantifier $\forall$, so it is not free. Therefore, $\forall x P(x)$ is a closed formula.

## Quantifier

[Wikipedia: Quantifier (logic)](https://en.wikipedia.org/wiki/Quantifier_(logic))

In logic, a quantifier is an operator that specifies how many individuals in the domain of discourse satisfy an open formula. For instance, the universal quantifier $\forall$ in the first order formula $\forall x P(x)$ expresses that everything in the domain satisfies the property denoted by $P$. On the other hand, the existential quantifier $\exists$ in the formula $\exists x P(x)$ expresses that there exists something in the domain which satisfies that property. A formula where a quantifier takes widest scope is called a quantified formula. A quantified formula must contain a bound variable and a subformula specifying a property of the referent of that variable.

## Quantifier Alternation

[The Tale of the Quantifier Alternation Hierarchy of First-Order Logic over Words](https://www.labri.fr/perso/tplace/Files/surveyqalt.pdf)

Quantifier alternation is a natural such measure: a language is considered complicated when we need many switches between blocks of $\exists$ quantifiers and blocks of $\forall$ quantifiers to express it.

Our methodology involves modeling protocols using general (uninterpreted) first-order logic, and then systematically transforming the model to obtain a model and an inductive invariant that are decidable to check.

[ChatGPT: Some Example of Quantifier Alternation](https://poe.com/s/tofgQfDVSeQUyosAlrW5)

In first-order logic, a quantifier alternation occurs whenever an existential quantifier ($\exists$, "there exists") is followed by a universal quantifier ($\forall$, "for all"), or vice versa. The alternation between these two types of quantifiers can increase the complexity of a logical formula.

Here are a couple of examples:

+ $\forall x \exists y P(x, y)$: There is one alternation of quantifiers here, from the universal quantifier ($\forall x$) to the existential quantifier ($\exists y$).
+ $\exists x \forall y \exists z P(x, y, z)$: There are two alternations of quantifiers here, from the existential quantifier ($\exists x$) to the universal quantifier ($\forall y$), and then back to an existential quantifier ($\exists z$).

## Quantifier Alternation Graph

## Completeness and Soundness

[What is the difference between Completeness and Soundness in first order logic?](https://math.stackexchange.com/questions/105575/what-is-the-difference-between-completeness-and-soundness-in-first-order-logic)

In more detail: Think of $\Sigma$ as a set of hypotheses, and $\Phi$ as a statement we are trying to prove. When we say $\Sigma \vDash \Phi$, we are saying that $\Sigma$ logically implies $\Phi$, i.e., in every circumstance in which $\Sigma$ is true, then $\Phi$ is true. Informally, $\Phi$ is "right" given $\Sigma$.

When we say $\Sigma \vdash \Phi$, on the other hand, we must have some set of rules of proof (sometimes called "inference rules") in mind. Usually these rules have the form, "if you start with some particular statements, then you can derive these other statements". If you can derive $\Phi$ starting from $\Sigma$, then we say that $\Sigma \vdash \Phi$, or that $\Phi$ is provable from $\Sigma$.

We are thinking of a proof as something used to convince others, so it's important that the rules for $\vdash$ are mechanical enough so that another person or a computer can check a purported proof (this is different from saying that the other person/computer could create the proof, which we do not require).

Soundness states: $\Sigma \vdash \Phi$ implies $\Sigma \vDash \Phi$. If you can prove $\Phi$ from $\Sigma$, then $\Phi$ is true given $\Sigma$. Put differently, if $\Phi$ is not true (given $\Sigma$ ), then you can't prove $\Phi$ from $\Sigma$. Informally: "You can't prove anything that's wrong."

Completeness states: $\Sigma \vDash \Phi$ imples $\Sigma \vdash \Phi$. If $\Phi$ is true given $\Sigma$, then you can prove $\Phi$ from $\Sigma$. Informally: "You can prove anything that's right."

## Higher-order Reasoning

[ChatGPT: Higher-order reasoning in the context of consensus protocols](https://poe.com/s/M8TpkGLv98foBM7nLpXD)

In the context of consensus protocols like Paxos, higher-order reasoning typically refers to reasoning about sets of nodes and their relationships to each other, rather than reasoning solely about individual nodes. For example, in Paxos, a quorum is a set of nodes that have agreed on a particular value. Higher-order reasoning is required to ensure that a majority of nodes in the system agree on a value, so that the system can reach consensus. This involves reasoning about **sets** of nodes (i.e., quorums) and their **relationships** to each other, such as the fact that any two quorums must overlap by at least one node in order to ensure progress.

## Sort

[ChatGPT: Sort](https://poe.com/s/H1EvC5bUlGwhxOps3wW1)

In many-sorted logic, each variable is assigned a sort, which specifies the domain of objects that the variable can take on. For example, in a first-order logic language with sorts for integers and strings, a variable x of sort integer can take on values such as 0, 1, -1, 2, etc., while a variable y of sort string can take on values such as "hello", "world", "abc", etc.

## Derived Relations

[ChatGPT: Derived Relations](https://poe.com/s/dfRgDsRYKKYCFeo5vziz)

Derived relations are new relations that are introduced to a logic formula to replace a part of it, usually to simplify the formula or to eliminate certain structures, such as quantifier alternations.

Suppose you have the formula $\forall x \exists y P(x, y)$. We introduce a new relation, $Q(x)$, which is defined to be true if and only if there exists a $y$ such that $P(x, y)$ holds true. This new relation, $Q(x)$, is a derived relation because it is derived from the original relation, $P(x, y)$. With this derived relation, we can replace the original formula with a simpler one: $\forall x Q(x)$. This new formula does not involve any quantifier alternations.

## Finite Model Property

[ChatGPT: What does "finite model property" means?](https://poe.com/s/dQFfF6AQ3nexwZXqma8b)

A "model" in this context refers to a specific assignment of values to variables that makes a given formula true. If a formula has the finite model property, then it means that we can find such an assignment without needing an infinite number of elements.

The statement "we can find such an assignment without needing an infinite number of elements" means that if a formula is satisfiable, there exists a model -- a specific assignment of values to variables -- that makes the formula true, and this model can be constructed using a finite set of elements. It does not necessarily mean that we can always easily find this model or that we don't have to search through potentially many elements to find it.

[Wikipedia: Finite model property](https://en.wikipedia.org/wiki/Finite_model_property)

## Interpreted Domain

## Uninterpreted First-order Logic

# Introduction

## Comparing EPR and TLA: Understanding the Differences

The goal is that the system can reliably produce in finite time either a proof that the invariant is inductive or display a comprehensible counterexample to induction (CTI). Such a task seems very difficult since these protocols are usually expressed in rich programming languages in which automatically checking inductive invariants is both undecidable and very hard in practice.

Expressing the verification conditions in a decidable logic with a small model property (e.g., EPR) will guarantee Completeness and Finite Counterexamples. However, it is not clear how to model complex protocols like Paxos in such logics. Consensus protocols such as Paxos often require higher-order reasoning about sets of nodes (majority sets or quorums), combined with complex quantification. In fact, some researchers conjectured that decidable logics are too restrictive to be useful.

Systems such as Alloy and TLA have already been used for finding bugs in protocols and inductive invariants. However, in contrast to our approach, they cannot automatically produce proofs for inductiveness (Completeness).

## A Reusable Verification Methodology

Our methodology allows the expression of complex protocols and systems, while guaranteeing that the verification conditions are expressed in EPR. EPR is supported by existing solvers:

+ [Z3Prover/z3: The Z3 Theorem Prover](https://github.com/Z3Prover/z3)
+ iProver
+ [vprover/vampire: The Vampire Theorem Prover](https://github.com/vprover/vampire)
+ [CVC4/CVC4-archived](https://github.com/CVC4/CVC4-archived)

The verification methodology is structured in the following way:

+ The first phase in our verification process is expressing the system and invariant in (undecidable) many-sorted first-order logic over uninterpreted structures.
+ We examine the quantifier alternation graph of the verification condition, which connects sorts that alternate in $\forall \exists$ quantification. When this graph contains cycles, solvers such as Z3 often diverge into infinite loops while instantiating quantifiers. This issue is avoided when the graph is acyclic, in which case the verification condition is essentially in EPR. Therefore, the second phase of our methodology provides a systematic way to soundly eliminate the cycles.
  + The most creative part in our methodology is adding derived relations and rewriting the code to break the cycles in the quantifier alternation graph. The main idea is to capture an existential formula by a derived relation, and then to use the derived relation as a substitute for the formula, both in the code and in the invariant, thus eliminating some quantifier alternations.
  + The user is responsible for defining the derived relations and performing the rewrites.
  + The system automatically generates update code for the derived relations, and automatically checks the soundness of the rewrites.
  + For the generation of update code, we exploit the locality of updates, as relations (used for defining the derived relations) are updated by inserting a single entry at a time.
  + We identify a class of formulas for which this automatic procedure is always possible and use this class for verifying the Paxos protocols.

# Background: Verification Using EPR

## Transition Systems in First Order Logic

RML commands include nondeterministic choice, sequential composition, and updates to constant symbols, function symbols and relation symbols (representing the system’s state), where updates are expressed by first-order formulas.

We note that RML is Turing-complete, and remains so when $INIT$ and $TR$ are restricted to the EPR fragment.

INV == Spec (in TLA+) ?

## Extended Effectively Propositional Logic

Moreover, formulas in this fragment enjoy the finite model property, meaning that a satisfiable formula is guaranteed to have a finite model.

The size of this model is bounded by the total number of existential quantifiers and constants in the formula. The reason for this is that given an $\exists^* $\forall^*$ formula, we can obtain an equi-satisfiable quantifier-free formula by Skolemization, i.e., replacing the existentially quantified variables by constants, and then instantiating the universal quantifiers for all constants.

While EPR does not allow any function symbols nor quantifier alternation except $\exists^* $\forall^*$, it can be easily extended to allow stratified function symbols and quantifier alternation (as formalized below). The extension maintains both the finite model property and the decidability of the satisfiability problem.

Extended EPR. A formula $\varphi$ is stratified if its quantifier alternation graph is acyclic. The extended EPR fragment consists of all stratified formulas. This fragment maintains the finite model property and the decidability of EPR. The reason for this is that, after Skolemization, the vocabulary of a stratified formula can only generate a finite set of ground terms. This allows complete instantiation of the universal quantifiers in the Skolemized formula, as in EPR. In the sequel, whenever we say a formula is in EPR, we refer to the extended EPR fragment.

# Methodology for Decidable Verification

## Modeling in Uninterpreted First-Order Logic

### Axiomatizing Interpreted Domains

To express an interpreted domain, such as the natural numbers, in uninterpreted first-order logic, we add a sort that represents elements of the interpreted domain, and uninterpreted symbols to represent the interpreted symbols (e.g. a $\lt$ binary relation).

We capture **part** of the intended interpretation of the symbols by introducing axioms to the model. The axioms are a finite set of first-order logic formulas that are valid in the interpreted domain. By adding them to the model, we allow the proof of verification conditions to rely on these axioms. By using only axioms that are valid in the interpreted domain, we guarantee that any invariant proved for the first-order model is also valid for the actual system.

One important example for axioms expressible in first-order logic is the axiomatization of total orders.

### Expressing Higher-Order Logic

Another hurdle to using first-order logic is the fact that algorithms and their invariants often use sets and functions as first class values. In such cases, the invariants needed to prove the algorithms will usually include higher-order quantification.

In this case, we can add a new first-order sort called map, and a function symbol apply?
不是说好了不用 function 吗？

While this encoding is sound (as long as we only use axioms that are valid in the higher-order interpretation), it cannot be made complete due to the limitation of first-order logic. However, we did not experience this incompleteness to be a practical hurdle for verification in first-order logic.

### Semi-Bounded Verification
