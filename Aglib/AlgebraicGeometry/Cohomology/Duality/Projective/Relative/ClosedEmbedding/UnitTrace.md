# Original chosen-embedding trace and structural unit

[UnitTrace.lean](UnitTrace.lean) works on the actual source
`S = Hom(O_Z[0], K[n])`. Here K is the original closed right-adjoint value
at the literal `relativeTopDifferentialCoefficientsFunctor` applied to the
base structure unit. Concentration and a canonical-module frame are not
used to construct this source or its trace.

`relativeClosedEmbeddingSerreMap_apply_counit` identifies the existing
Serre map with the original inverse adjunction, its supplied-resolution
counit, original derived pushforward, and installed projective trace.
`relativeClosedEmbeddingDegreeZeroSerreMap` retains this map and
postcomposes with the native `single_n(N)[n] ≅ single_0(N)` isomorphism.
Its source naturality uses the original multiplication endomorphism on Z.

The module-valued map is constructed from the fully faithful native
bounded-below inclusion and `moduleDerivedGlobalSectionsPushforwardCompIso`.
At the affine target, quasicoherent acyclicity proves that the actual
derived single unit is invertible. Its inverse and the original `ΓSpecIso`
give `affineDerivedStructureTargetIso`. The original structural unit maps
to the identity under that normalization.

For the given scalar map `σ : R →+* A`,
`moduleGlobalSectionsRestrictIso` is the native identity on sections under
successive scalar restriction. `moduleDerivedGlobalSectionsRestrictIso`
derives this same map and retains both original single units. Its full
derived-category form is `moduleDerivedStructureRestrictionIso`.
`moduleRestrictedDerivedStructureUnit_full` displays literal restriction
of `moduleDerivedStructureUnit`, together with the native exact-single
comparison. No map from A to R is introduced.

The scalar square is proved before forgetting the A-action. It uses the
original structural map on sections and
`rightDerivedSingleUnit_coefficient_naturality` applied to multiplication
on the structure module. The resulting action on derived sections is the
actual functor image of that multiplication. A separate linearity theorem
for the entire right-derived functor is unnecessary.

`chosenEmbeddingUnitFunctional` is the actual R-linear map `A → R`
obtained by precomposing the same comparison with that restricted unit.
Native full faithfulness of the single functor fixes its underlying map.
`chosenEmbeddingTraceCoinduced` packages it as an A-linear map from S to
the original `(ModuleCat.coextendScalars σ).obj (ModuleCat.of R R)`.
Its two evaluation theorems give

    Tr_A(s)(a) = Tr_R(a • s)
              = (Phi0(s) after Res(eta_A))(a).

All single and restriction isomorphisms in the second expression are
displayed in `chosenEmbeddingTraceCoinduced_eq_original_unit`.
`chosenEmbeddingTraceBase_geometric_unit` also identifies the base-unit
formula with the original geometric pushforward structure unit followed
by the same Serre map. The required comparison is derived from the
existing composite-unit equation, rather than assumed as a trace law.

The algebraic trace equation works for any commutative scalar map with
the stated structural compatibility. For the actual chosen embedding and
original map `g : Z → Spec A`,
`chosenEmbeddingBaseScalar_eq_of_triangle` derives that compatibility from
`i ≫ p = g ≫ Spec.map σ` using the original `ΓSpecIso` naturality.
Thus the intended finite injective local map is used unchanged; finiteness,
injectivity, properness and birationality are unnecessary for this
source-local trace equation itself.

The source remains the actual derived Hom. Transport to sections of the
concentrated canonical module and to a supplied HomComplex/Postnikov
model are subsequent consumers of the normalized concentration and
original resolution comparisons. This leaf does not assert an
embedding-independent proper/finite trace identity or
Grauert--Riemenschneider vanishing.

The base-trace restricted-scalar theorem retains the original structural
identity `hα` as an explicit input before the scalar `r`.
`moduleAffineStructureSectionsIso_inv` records the original structural
section map used to normalize the affine coefficient isomorphism.

The actual structural sections, derived object and unit are defined in
[Proper/DerivedStructure/Basic](../../../../Proper/DerivedStructure/Basic.md).
The original composite-unit law is supplied by
[GlobalSectionsComposition/SingleUnit](../../../../Functoriality/GlobalSectionsComposition/SingleUnit.md).
This trace construction uses these lower interfaces directly, independently
of the H1/Postnikov assembly in the full `Proper/DerivedStructure` module.
