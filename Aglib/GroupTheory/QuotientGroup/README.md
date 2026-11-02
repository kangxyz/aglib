# Power maps modulo cyclic subgroups

`Power` extends `QuotientGroup` on the actual quotient `G ⧸ Subgroup.zpowers p`.
A displayed power relation constructs natural or signed power maps with literal
representative formulas. Kernel cardinality for arbitrary commutative groups
retains power surjectivity and infinite order of both period elements.

For units of an algebraically closed field, power surjectivity is proved.
Kernel and fibre cardinalities retain characteristic zero, positive power and
infinite-order hypotheses. The signed comparison uses actual inversion.
These results precede downstream period-quotient applications and assert no
analytic uniformization, completion result or scheme-theoretic degree.

[Nsmul](Nsmul.lean) supplies the native map modulo `n`, representative, identity,
composition and naturality equations, and an equivalence induced by a surjection
with `n`-divisible kernel. Its integer specialization targets `ZMod n` and
retains the whole projection equation. Exactness transport identifies the whole
kernel of a boundary with the range of multiplication. Every `n`, including
zero and one, is allowed; no section or replacement quotient is chosen.
