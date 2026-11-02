# Degree-zero coefficient Serre comparison

Source: [CoefficientsTopHom.lean](CoefficientsTopHom.lean).

`projectiveDerivedSerreMapCoefficients_zero_bijective` concerns the
original degree-zero coefficient Serre map over a commutative Noetherian
ring `R`, with finite coordinates `ι ≃ Fin (n+1)`, arbitrary
`J : ModuleCat R`, and an affine-locally finite-type module sheaf `M` on
that same projective space. Quasicoherence of `M` is derived from this
finite-type hypothesis; no additional coefficient-flatness premise is used.

The Hom/tensor comparison uses the actual
`twistingTensorTildeSectionsIso` from
`TwistCohomology.Coefficients.Sections`.
The normalization and coefficient-naturality proofs retain that forward
section map, the original Ext/cohomology actions and
`moduleTensorTildeSectionsMap_naturality_coefficients`.
This section comparison is separate from the derived-model naturality
interface.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Derived/CoefficientsCoherent](CoefficientsCoherent.lean).
