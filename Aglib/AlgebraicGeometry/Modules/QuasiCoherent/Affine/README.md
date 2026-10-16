# Affine quasicoherent and finite-type comparison

For a commutative ring object `R`, actual module sheaves on `Spec R` have the native tilde/global-section interface. [Pullback](Pullback.lean) gives `Scheme.Modules.tildePullbackIso`, and [Pushforward](Pushforward.lean) gives `tildePushforwardIso`, using actual extension/restriction of scalars. Their section/unit formulas are in [PullbackSections](PullbackSections.lean), [ScalarAdjunction](ScalarAdjunction.lean) and the restriction coefficient/section leaves.

In `Scheme.Modules.QuasiCoherent`, [FiniteTypeCategory](FiniteTypeCategory.lean) defines `AffineQuasicoherent`, `AffineFiniteType` and `affineFiniteTypeModuleEquivalence`. [FiniteTypeProperty](FiniteTypeProperty.lean) defines `affineFiniteSheaf` as quasicoherence plus finite global sections. [FiniteTypeComparison](FiniteTypeComparison.lean) compares the global affine-locally finite-type category with these affine objects and actual finite modules. These object/equivalence interfaces are general commutative-ring results; their Noetherian abelian/exact specialization lives separately in [Coherent/Affine](../../Coherent/Affine/README.md).

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
