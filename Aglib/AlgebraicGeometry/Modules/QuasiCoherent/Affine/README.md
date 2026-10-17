# Affine quasicoherent and finite-type comparison

For a commutative ring object `R`, actual module sheaves on `Spec R` have the native tilde/global-section interface. [Pullback](Pullback.lean) gives `Scheme.Modules.tildePullbackIso`, and [Pushforward](Pushforward.lean) gives `tildePushforwardIso`, using actual extension/restriction of scalars. Their section/unit formulas are in [PullbackSections](PullbackSections.lean), [ScalarAdjunction](ScalarAdjunction.lean) and the restriction coefficient/section leaves.

In `Scheme.Modules.QuasiCoherent`, [FiniteTypeCategory](FiniteTypeCategory.lean) defines `AffineQuasicoherent`, `AffineFiniteType` and `affineFiniteTypeModuleEquivalence`. [FiniteTypeProperty](FiniteTypeProperty.lean) defines `affineFiniteSheaf` as quasicoherence plus finite global sections. [FiniteTypeComparison](FiniteTypeComparison.lean) compares the global affine-locally finite-type category with these affine objects and actual finite modules. These object/equivalence interfaces are general commutative-ring results; their Noetherian abelian/exact specialization lives separately in [Coherent/Affine](../../Coherent/Affine/README.md).

[TildePullback](TildePullback.lean) proves the compatibility of `tildePullbackIso` with composition: for `a : R ⟶ S` and `b : S ⟶ T`, `tildePullbackIso_comp_hom` identifies `pullbackCongr`, `(pullbackComp _ _).inv`, `tildePullbackIso a` pulled back along `Spec.map b` and `tildePullbackIso b` with `tildePullbackIso (a ≫ b)` followed by `tilde` of `ModuleCat.extendScalarsComp a.hom b.hom`; `tildePullbackIso_comp_hom_app` is the componentwise form for an arbitrary proof of `Spec.map (a ≫ b) = Spec.map b ≫ Spec.map a`. The proof identifies `tildePullbackIso φ` as the conjugate of `pushforwardGlobalSectionsIso φ` (`conjugateEquiv_tildePullbackIso_hom`) and reduces to an identity of right adjoints on sections; `Adjunction.conjugateEquiv_ofNatIsoRight_id` is a generic mate lemma whose intended owner is Mathlib's `Adjunction/Mates.lean`. No quasicoherence hypothesis is used. Its consumer is [affine faithfully flat descent](../../../Descent/Modules/Fppf/README.md).

[FiniteGenerators](FiniteGenerators.lean) and [FiniteType](FiniteType.lean) derive finite global sections from actual finite global/local generators and compare the finite-type witnesses. [FiniteTypeRestriction](FiniteTypeRestriction.lean) identifies actual principal-open restriction with module localization. [FiniteTypeSupport](FiniteTypeSupport.lean) proves closed support for affine finite-type quasicoherent objects over any commutative ring and identifies the actual supported-away property; Noetherianity is not needed for that closed-support conclusion.

[Exact](Exact.lean), [Exactness](Exactness.lean), [TildeExact](TildeExact.lean), [Sections](Sections.lean) and [Support](Support.lean) record the actual ambient affine exactness, section and support comparisons. Quasicoherent affine acyclicity uses these maps over arbitrary commutative rings. Focused imports use the named `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine` leaves.

Consumers are finite-type/coherent comparison, finite and closed direct image, finite locally free affine sections, scalar restriction and [actual affine cohomology](../../../Cohomology/Affine/README.md). A finite-projective equivalence is not part of the selected finite-local-free global-generation result.

[ClosedImmersion](ClosedImmersion.lean) owns the unguarded quotient-ring `closedRing`, actual `closedMap` and finite-type quasicoherent pushforward results in `Scheme.Modules.QuasiCoherent.Pushforward.ClosedImmersion.Ideal`. The base commutative ring and ideal are arbitrary; the source and target are their actual affine spectra. The later coherent exact/killed-sheaf equivalence remains in the guarded [coherent closed-immersion family](../../Coherent/Pushforward/ClosedImmersion/README.md).

[Free](Free.lean) gives `Scheme.Modules.tildeBasisIso`: the actual tilde functor sends a module basis to the free sheaf on the same index type via the canonical Finsupp comparison. This leaf needs no Noetherian or base-change hypothesis and is lower than the smooth differential-rank and affine module-base-change proofs.

[Chart](Chart.lean) identifies actual sections on an affine chart with the corresponding Spec module on its original scalars, and transfers a module basis through the existing tilde/Finsupp comparison.

[Morphisms](Morphisms.lean), imported as `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms`, supplies actual affine QC kernel comparisons, section denominator clearing and scalar-extended injectivity from actual pullback monicity. Its adjunction hom-equivalence equations retain the canonical comparison directions and actual unit maps.

[Isomorphisms](Isomorphisms.lean) detects an isomorphism through global sections and the
canonical `fromTildeΓ` maps. [Finite-type extension](../FiniteType/Extension/README.md) and
[restriction comparisons](../FiniteType/Restriction/README.md) keep their arbitrary-ring
finite-type statements below the coherent layer.

The affine base-change and finite-flat local-freeness suppliers do not retire
the fifteen original R5 Spec comparison interfaces. Nineteen actual equality
witnesses for their canonical maps pass native checks and independent correspondence
review. Four R5 caller transports remain pending, so the original producer/caller
interfaces remain unretired. The accepted comparisons are actual arrow equations,
not type agreement alone.

[Annihilator](Annihilator.lean) transports actual affine-section annihilation
to every subopen, which need not be affine. The original scalar-center
endomorphism vanishes by the native tilde/global-section counit; the
affine-chart restriction unit then retains the original restricted scalar
and section action. Quasicoherence is needed only on the affine mother
chart. There is no finite-generation or Noetherian hypothesis. The native
restriction map sends the original section annihilator into the subopen
section annihilator.

The source passed alone with receipt `1792113018497882000-92487` in
3.4 seconds at the default budget. `AffineAnnihilatorConsumer.lean` passed
with receipt `1792113077151022000-93137`, including arbitrary subopens;
all four inspected declarations use only the three standard axioms.

[Injective](Injective.lean) proves that the original affine sections functor
preserves injective objects, using its adjunction with exact tilde. It sends
any bounded-below injective complex to a K-injective module complex. No term
is assumed quasicoherent; exactness of the sections resolution of a QC
coefficient remains the separate affine-acyclicity theorem. These original
injectives are used by the local closed-right-adjoint/Koszul Ext comparison.

[ScalarAdjunction/Counit](ScalarAdjunction/Counit.lean) retains the original
tilde counit square under the scalar/geometric Hom adjoints for arbitrary
module sheaves. Neither quasicoherence nor flatness is needed for this
termwise comparison. Its [focused guide](ScalarAdjunction/README.md) records
the resolved-base-change consumer.

[Free](Free.lean) gives `tildeBasisIso`: a native module basis identifies the
actual tilde sheaf with the native free sheaf on the same index type. Smooth
affine differential charts use this comparison.

[Free/Sections](Free/Sections.lean) identifies original localized basis vectors
and native free sections under the existing `tildeBasisIso`, in both directions.
The original map is unchanged. Its supporting summand equation uses the native
tilde/Finsupp coproduct comparison. The ring, module, basis, index type and opens
retain their native universes, with no finite, field, Noetherian, or nontrivial
premise. The actual projective Euler coordinate and Kähler frames consume these
section formulas.
