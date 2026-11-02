# Literal root-algebra base change

`BivariateTensor` constructs `AdjoinRoot.bivariateTensorEquiv` by the canonical
polynomial-tensor equivalence and Mathlib's root-algebra base change. The source
and target polynomial equality is supplied explicitly; no monicity, domain or
curve hypothesis is inferred. Root and coefficient formulas retain the literal
forward map. One implementation replaces the two identical source constructions.

[PowerRelation](PowerRelation.lean) presents the original domain
`A`-algebra `B` by `X^p-C a` from a normal domain `A`, torsion-free
scalar action, nonzero `p`, actual `finrank A B=p`, the original equation
`algebraMap A B a=z^p` and `Algebra.adjoin A {z}=⊤`.
The root remains `z` and the forward map remains `Polynomial.aeval z`.
Primality, characteristic, locality and Noetherianity are not added.
The DVR and field pure-degree constructors reuse this presentation.
