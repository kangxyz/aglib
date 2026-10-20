# Characteristic-zero curve isogenies

[Etale.lean](Etale.lean) proves `Curve.finite_hom_etale_of_charZero` on the
actual native group homomorphism. Its field is arbitrary, in an arbitrary
universe, with `Field` and `CharZero`. Both group schemes carry the existing
`Curve.Properties` predicate: smooth of relative dimension one, proper and
geometrically connected. Finiteness and surjectivity concern the literal
`f.hom.hom.left`; the conclusion is `Etale f.hom.hom.left`.

`Curve.charZeroFiniteCurveGroupHomEtale` is the exact explicit-argument family
accepted by [the conditional native consumer](../../Group/CurveIsogeny.lean).
`Curve.pointed_dominant_finite_etale_of_charZero` binds that family to the
existing consumer, retaining its actual field schemes, prescribed origins,
pointed group laws, dominant morphism and origin equation. It returns the
homomorphism property, finiteness, etaleness and surjectivity of that same map.

The proof first proves finiteness of the actual generic-field map using the
canonical generic-fibre isomorphism. Characteristic zero makes that extension
separable, hence formally etale. The existing stalk-locality theorem supplies
an etale source neighborhood. Over an algebraically closed field, the scheme
is Jacobson and its closed points are rational; literal translations of that
neighborhood cover it. Finally, the native group base change along
`Spec (AlgebraicClosure k) → Spec k` is cartesian, and Mathlib's fpqc descent
of etaleness returns the conclusion for the original map.

Lower reusable statements expose the finite generic-field map, its formally
etale generic stalk in characteristic zero, the generic etale neighborhood,
actual translation isomorphisms and equivariance, and propagation from a
nonempty etale source open. No new generic-etaleness, translation or flatness
theorem-family input is introduced.

Target identity: `EG-SEPARABLE-ISOGENY-ETALE`, from the read-only assignment
packet `AGLIB_PROOF_TASKS.json`. The source target is
`R5Lab.AlgebraicGeometry.Curves.Isogenies.FieldFinite`, declaration
`CharZeroFiniteCurveGroupHomEtale`, at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`7bedffaeee588fc70a0a0257eda4d44e8f64bcdaf4e5a6270f22558dfa1241b0`.
That source declares a theorem-family obligation; the producer here supplies
its proof. No Picard or Hilbert representability, purity, multiplication-map
criterion or arithmetic marking is used.

The focused interface client is
[CharZeroCurveIsogeny.lean](../../../../AglibTest/CharZeroCurveIsogeny.lean).
