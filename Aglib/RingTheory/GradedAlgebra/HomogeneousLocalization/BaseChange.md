# Scalar extension of the original degree-one chart

[BaseChange.lean](BaseChange.lean) constructs the actual algebra equivalence

    S ⊗_R Away(G,f) ≃ Away(G_S,1 ⊗ f)

for an actual commutative graded `R`-algebra `D`, its natural-number
grading `G`, an original `f ∈ G 1`, and an arbitrary commutative
`R`-algebra `S`. Here `G_S` is Mathlib's grading on the full tensor algebra
`S ⊗_R D`. No passage to an image algebra inside a polynomial ring occurs.

`scalarAlgebra` is the original coefficient action through `G 0`.
`degreeOneQuotientAlgEquiv` promotes the explicit dehomogenization ring
equivalence using its proved degree-zero formula. `scalarExtensionEquiv`
then composes that equivalence, the native tensor/quotient equivalence,
the actual equality of the mapped dehomogenizing ideals, and the inverse
dehomogenization equivalence over `S`.

`scalarExtensionEquiv_tmul_mk` states the actual map on the original
fractions: `s ⊗ (a/f^n)` goes to `(s ⊗ a)/(1 ⊗ f)^n`.
This includes the degree-zero coefficient maps and degree-one ratios.
No flatness, domain, nonzero, Noetherianity or finite-generation condition
is imposed. Zero and nilpotent denominators remain included.

The current consumer is the nonflat Rees/Proj chart comparison in the
projective presentation of a base-changed blowup. The scheme pullback
square, tautological-quotient matching, coordinate graph closedness and
point-chain projective embedding remain separate obligations.
