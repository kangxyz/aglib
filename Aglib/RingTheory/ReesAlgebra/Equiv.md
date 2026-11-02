# Native Rees equivalences

For an arbitrary ring equivalence `e : A ≃+* B` and original ideal `I`,
`reesAlgebra.mapEquiv e I` promotes the already existing coefficientwise
`reesAlgebra.map e.toRingHom I` by its proved bijectivity. Its codomain is the
original `reesAlgebra (I.map e.toRingHom)`, not an alternate Rees construction.
The forward application and polynomial coefficient equations remain literal.

Injectivity is native polynomial-map injectivity. A target Rees polynomial
maps coefficientwise through the inverse equivalence; original ideal map and
power membership show that this preimage belongs to the original Rees algebra.
The source and target universes are independent. No local, Noetherian, field,
flatness, or finite-generation hypotheses are used.
