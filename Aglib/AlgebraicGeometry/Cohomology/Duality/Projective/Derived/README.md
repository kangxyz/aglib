# Derived projective trace and Serre comparison

`Trace.lean` constructs the native trace for the existing dualizing twist
`omega = twistingSheaf R ι (-(Fintype.card ι : ℤ))`. The base is an arbitrary
commutative ring, the coordinate type retains its common geometric universe,
and `e : ι ≃ Fin (n + 1)` specifies the dimension. Dimension zero is included.
No Noetherianity, base flatness, or additional theorem-family input is required.

`projectiveDerivedResidueTwist` is the actual installed
`(moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus` on the original
coefficient single, followed by `DerivedCategory.Plus.ι` into the full derived
category of `ModuleCat R`. Here `P = ProjectiveSpace R ι` and `α` is the original
structural map through `toSpec` and `ΓSpecIso`. No replacement right-derived
functor or scalar action is introduced.

`projectiveDerivedResidueTwist_isZero_homology`, `_isGE`, and `_isLE` prove
concentration in degree `n`. The nonnegative-degree proof uses the original
Laurent comparison and the proved negative-degree native simplex/weight
vanishing. The negative-degree proof uses the installed right-derived functor's
lower-bound theorem. These are proved suppliers, not an assumed concentration
family.

`projectiveDerivedTraceHomologyLinearEquiv` composes the released comparison
with original `Sheaf.H` and the unchanged `projectiveTraceLinearEquiv`.
`projectiveDerivedTrace` reconstructs the concentrated source using
`DerivedCategory.isoSingleHomology` and applies the native single functor to
that linear map. Its target is `single_n (ModuleCat.of R R) = R[-n]`, and
`projectiveDerivedTrace_isIso` proves that this arrow is an isomorphism.

The forward map is fixed by `projectiveDerivedTrace_homology` and
`projectiveDerivedTrace_homology_apply`. For every supplied injective resolution
`I` of the same original twist and every native homology class `x`, the latter
states the literal equation

```text
singleFunctorCompHomologyFunctorIso.hom (Hn(trace) x)
  = projectiveTrace (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv I n x).
```

Thus the original Laurent-cycle trace remains the same all-minus-one
coefficient with positive sign, through `projectiveTrace_laurent_homologyπ`.
The comparison does not depend on which injective resolution is supplied.

`projectiveDerivedTrace_smul` proves the actual derived-arrow equation

```text
Plus.ι.map (RFplus.map (single_0.map (r • id_omega))) ≫ trace = r • trace.
```

The source scalar is the original `moduleCategoryLinearOfHom P α` action;
the target scalar is the native linear structure on the full derived category.
The proof uses original cohomology coefficient naturality and detects the
arrow equality on degree-`n` homology. It needs no generic RF-linearity
assumption or new global instance.

The trace supplies the first input for affine-base relative Serre duality.
The following comparison retains this original trace; bijectivity remains a
separate mathematical step.

## Canonical comparison into full derived Hom

`Comparison.lean` supplies `projectiveDerivedSerreMap R ι n e M i` for every
actual module coefficient `M` and every `i : ℕ`, with no coherence, Noetherianity,
flatness, source bound or duality input. Its type is the native linear map

```text
Ext_X^i(M, omega) →ₗ[R]
  Hom_D(R)(F(single_0 M), (single_n R)⟦i⟧),
F = Γα.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι.
```

Thus the target is literal full derived Hom into `R[i-n]`, retaining higher
base-ring Ext terms. `projectiveDerivedSerreMap_apply` fixes its original
forward arrow as

```text
ShiftedHom.map x.homPlus F ≫ (shiftFunctor D(R) i).map projectiveDerivedTrace.
```

The native `Ext.homPlus` adapter and `ShiftedHom.map` supply the original
bounded-below lift and installed shift comparison. There is no replacement
RF map. Additivity uses the native additive lift and functor. Linearity rewrites
the original Ext scalar as postcomposition by `r • id_omega`, then uses
`projectiveDerivedTrace_smul` and native target-shift linearity; no generic
RF-linear instance is required.

`projectiveDerivedSerreMap_comp` preserves original Yoneda precomposition in
all nonnegative degrees. Its degree-zero case
`projectiveDerivedSerreMap_naturality` is natural for every actual coefficient
map. `projectiveDerivedSerreMap_extClass` identifies the original unsigned
extension class with the actual `singleTrianglePlus.mor₃`, mapped through `F`.
This is the unsigned boundary: the protected native `Ext.δ` separately
multiplies extension-class precomposition by `Int.negOnePow j` in target Ext
degree `j`.

`projectiveDerivedSerreMap_mk₀` identifies degree zero with the original
coefficient map followed by trace, through the native degree-zero shift
comparison. `projectiveDerivedSerreMap_mk₀_homology_apply` proves that its
unshifted degree-zero homology functional is exactly the existing
`projectiveTopSerreMap`, through every supplied injective resolution of `M`.
This normalization holds for arbitrary `M`; it does not assert that every
derived Hom map is determined by top homology without a source upper bound.

## Degree-zero bijectivity over a Noetherian base

`TopHom.lean` proves `projectiveDerivedGlobalSectionsSingle_isLE` for every
quasicoherent module over an arbitrary commutative base ring. It transfers the
proved original projective cohomological-dimension bound through the actual
resolution/cohomology comparison; no concentration family is assumed.

`projectiveDerivedSerreMap_zero_bijective` proves bijectivity of the unchanged
`projectiveDerivedSerreMap R ι n e M 0` over a Noetherian ring for the original
coherent hypothesis `affineLocallyFiniteType P M`. No flatness or perfectness of
`M` is required, and `n = 0` is included. The proof uses native Ext in degree
zero, the actual shift-zero comparison, `DerivedCategory.homToSingleAddEquiv`,
and the original resolution/cohomology equivalence. Its transported forward
map is literally `projectiveTopSerreMap`; the established top duality theorem
therefore supplies bijectivity of this same comparison.

## All-degree relative Serre duality over an affine Noetherian base

`Coherent.lean` proves `projectiveDerivedSerreMap_bijective` for every
`i : ℕ`, with exactly the same Noetherian-ring and original coherent-module
hypotheses. `projectiveDerivedSerreDuality` packages this unchanged comparison
as an R-linear equivalence

```text
Ext_X^i(M, omega) ≃ₗ[R]
  Hom_D(R)(F(single_0 M), (single_n R)⟦i⟧).
```

`projectiveDerivedSerreDuality_apply` is definitionally the existing
`projectiveDerivedSerreMap`. Its forward map therefore retains the original
trace, structural scalars, coefficient naturality, degree-zero top Serre map,
and actual unsigned extension compatibility proved in `Comparison.lean`.
No flatness or perfectness of `M`, or regularity of the base ring, is required.

The induction uses
`exists_uniformNegativeTwistCoherentPresentation` beyond the original residue
bound. Its presentation has the original quotient map and actual coherent
kernel. `negativeTwistCoproductExt_dualizing_subsingleton` supplies positive
source Ext vanishing for the same finite negative-twist sum.
`negativeTwistCoproductDerivedHom_subsingleton` proves positive target Hom
vanishing over every commutative ring: the actual resolution/cohomology
comparison and unchanged negative Laurent vanishing concentrate RΓ of that
sum in degree `n`; original finite-coproduct cohomology is free, hence its
native homology object is projective. The generic native projective-single
vanishing applies after the homology-normalized reconstruction.

The original unsigned Ext exact row and the native Yoneda exact row of the
actual mapped distinguished triangle are right exact. Coefficient naturality
and `projectiveDerivedSerreMap_extClass` identify their actual maps, so the
previous-degree bijections for the presentation and its coherent kernel
prove the next-degree bijection. The protected signed `Ext.δ` is not used in
this induction.

Dimension zero is included in every degree. No vanishing of Ext above `n`
is claimed over a singular base: the literal target keeps higher base-ring
Ext, including `R[1]` when `n = 0` and `i = 1`. General-base descent and
extensions to complex coefficients remain beyond this coherent-module,
affine-base endpoint.
