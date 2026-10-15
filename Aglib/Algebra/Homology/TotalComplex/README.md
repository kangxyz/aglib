# First-quadrant total complexes

Import `Aglib.Algebra.Homology.TotalComplex.FirstQuadrant` for `HomologicalComplex₂.FirstQuadrant` and its canonical maps. The ring is arbitrary; its universe and the module-object universe are independent. Totalization uses the native cochain total complex and finite antidiagonals.

`HomologicalComplex₂.quasiIso_total_of_rowwise` proves that a map whose every row is a quasi-isomorphism induces a quasi-isomorphism on total complexes. No upper degree bound, dimension bound or row splitting is assumed. The single-zero total inclusion/projection and augmentation comparisons are the actual coproduct-injection maps; the augmentation quasi-isomorphism theorems retain their rowwise premises.

[NatSigns](NatSigns.lean) fixes `ComplexShape.upNat_ε`, `upNat_ε₁`, `upNat_ε₂` and `upNat_σ`: in bidegree `(p,q)`, the native differential is horizontal plus `(-1)^p` times vertical, and flip contributes `(-1)^(p*q)`. [AddCommGrp](AddCommGrp.lean) transports the comparison through the equivalence of abelian groups and integer modules, with formulas characterized by the original injections.

For natural degrees with `p + q = n`, the active simp rule `HomologicalComplex₂.AddCommGrp.ι_mapTotalComparison_f` and its `_assoc` rule rewrite a total-summand injection followed by the degree-`n` comparison as the transported original injection.

Focused imports are the three `Aglib.Algebra.Homology.TotalComplex` leaves. The main consumers are actual scheme Cech/resolution comparison and canonical field-base-change comparison. The signs are part of that comparison's normalization, rather than interchangeable conventions.
