# Models and evaluation for the original two-layer triangle

Let `R` be regular local of finite dimension `d`. For an actual
distinguished triangle `T` with displayed endpoints `single 0 U` and
`single 1 H`, `CochainComplex.nonempty_twoLayerConeModel` constructs
`TwoLayerConeModel d U H T e₀ e₁` from finiteness of `H`. The record is
output data of this construction. Its source is the actual finite-projective
resolution of `single 1 H` supplied by
[FiniteComplexModel.lean](../../../../RingTheory/RegularLocalRing/FiniteComplexModel.lean).

K-projectivity represents the original connecting arrow by a chain map
`δ`, with the retained equation

```
Q.map δ = Q.map π ≫ e₁.hom ≫ T.mor₃ ≫ eU.inv.
```

The native cone triangle is compared with `T.rotate.rotate`. Its first
and second faces are the specified endpoint maps. The other two face
theorems retain the original unit and H1 projection, with the native
minus signs `-(T.mor₁[1])` and `-(T.mor₂[1])`. No vanishing of the
connecting map or splitting of `T` is assumed.

The resulting complex is `(mappingCone δ)[-1]`. It is supported in
`[min (1-d) 0,1]`, which is `[-1,1]` for dimension two. If `U` is finite
projective, its terms are finite projective. For an actual representative
`eK : Q.obj K ≅ T.obj₂`, `exists_quasiIso_to_representative` constructs
`q : model ⟶ K` and retains `Q.map q = derivedIso.hom ≫ eK.inv`.

The public interfaces in `CochainComplex.HomComplex` discharge the model
premise of the existing [Perfect.lean](Perfect.lean) evaluation theorem:

- `derivedEvaluation_single_isIso_of_restrictFinite` covers every native
  single degree, including the residue object in degree one, when its
  actual scalar restriction to `R` is finite.
- `derivedEvaluation_isIso_of_twoLayer` restricts the original `A`-triangle
  through the native exact functor. It requires the actual restrictions
  of `U` and `H` to be respectively finite projective and finite over `R`.
- `derivedEvaluation_isIso_of_unitPostnikov` uses the native Postnikov
  triangle of a specified unit and original H1. It takes the actual
  nonnegative and degree-one bounds, H0 isomorphism of that unit, and
  finiteness of the restricted original H1.

All three retain the original `A`-linear derived evaluation. Their
coefficient data are the existing universe-sized `W ≃ₗ[R] R`, a
K-injective complex `I`, its actual quasi-isomorphic augmentation from
`single 0 W`, and K-injectivity of the native coinduced coefficient.
The finite-projective model is constructed over `R`; no replacement
`A`-action is put on it.

For the surface consumer, the actual geometric unit, its H0 isomorphism,
the cohomological bounds, and finite H1 still require their geometric
proofs. This module does not assert those inputs or the identification of
the dual residue object. It provides the constructed model and evaluation
step once those actual inputs are supplied.
