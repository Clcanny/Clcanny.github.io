\* MC.tla
----------------------------------- MODULE MC -------------------------------
EXTENDS FastPaxos, TLC

CONSTANTS
v1, v2

CONSTANTS
c1, c2

CONSTANTS
a1, a2, a3, a4

const_Nat == 0..2
const_Val == {v1, v2}
const_Acceptor == {a1, a2, a3, a4}
const_FastNum == 1
const_Quorum(i) == {{a2, a3, a4},
                    {a1, a3, a4},
                    {a1, a2, a4},
                    {a1, a2, a3}}
const_Coord == {c1, c2}
const_CoordOf(i) == <<c1, c2>>[(i % Cardinality(const_Coord)) + 1]

symm == Permutations(const_Val) \union Permutations(const_Acceptor)
=============================================================================
