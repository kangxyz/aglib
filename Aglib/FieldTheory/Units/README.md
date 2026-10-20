# Finite subgroups of cyclic unit quotients

`CyclicQuotient.lean` studies the literal quotient `G ⧸ Subgroup.zpowers q` and
finite subgroups of a field's unit quotient. Under injectivity of integer powers
of `q`, it constructs an exponent homomorphism, positive image generator,
finite torsion kernel, and `KernelNormalForm` whose kernel is the existing
`QuotientGroup.zpowersPowerMap`. It also proves algebraicity and automorphism
invariance for the constructed period.

`CyclicQuotientDescent.lean` places those same elements inside the actual
relative algebraic closure. Original-field descent retains an algebraically
closed ambient field, characteristic zero of the source field, and the explicit
per-subgroup predicate `AlgebraicSubgroupStable`. This predicate is a supplied
action contract, not a theorem that a geometric isogeny supplies it.

Only norm-smallness consequences live in
[`Analysis/Normed/Field/CyclicQuotient`](../../Analysis/Normed/Field/CyclicQuotient.lean).
The pure field leaves import no analysis, completion, or curve theory. There is
no curve uniformization, incoming-isogeny classification, or scheme-kernel claim.
