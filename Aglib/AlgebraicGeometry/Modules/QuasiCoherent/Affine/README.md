# Affine quasicoherent and finite-type comparison

For a commutative ring object `R`, actual module sheaves on `Spec R` have the native tilde/global-section interface. [Pullback](Pullback.lean) gives `Scheme.Modules.tildePullbackIso`, and [Pushforward](Pushforward.lean) gives `tildePushforwardIso`, using actual extension/restriction of scalars. Their section/unit formulas are in [PullbackSections](PullbackSections.lean), [ScalarAdjunction](ScalarAdjunction.lean) and the restriction coefficient/section leaves.

In `Scheme.Modules.QuasiCoherent`, [FiniteTypeCategory](FiniteTypeCategory.lean) defines `AffineQuasicoherent`, `AffineFiniteType` and `affineFiniteTypeModuleEquivalence`. [FiniteTypeProperty](FiniteTypeProperty.lean) defines `affineFiniteSheaf` as quasicoherence plus finite global sections. [FiniteTypeComparison](FiniteTypeComparison.lean) compares the global affine-locally finite-type category with these affine objects and actual finite modules. These object/equivalence interfaces are general commutative-ring results; their Noetherian abelian/exact specialization lives separately in [Coherent/Affine](../../Coherent/Affine/README.md).

[FiniteGenerators](FiniteGenerators.lean) and [FiniteType](FiniteType.lean) derive finite global sections from actual finite global/local generators and compare the finite-type witnesses. [FiniteTypeRestriction](FiniteTypeRestriction.lean) identifies actual principal-open restriction with module localization. [FiniteTypeSupport](FiniteTypeSupport.lean) proves closed support for affine finite-type quasicoherent objects over any commutative ring and identifies the actual supported-away property; Noetherianity is not needed for that closed-support conclusion.

[Exact](Exact.lean), [Exactness](Exactness.lean), [TildeExact](TildeExact.lean), [Sections](Sections.lean) and [Support](Support.lean) record the actual ambient affine exactness, section and support comparisons. Quasicoherent affine acyclicity uses these maps over arbitrary commutative rings. Focused imports use the named `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine` leaves.

Consumers are finite-type/coherent comparison, finite and closed direct image, finite locally free affine sections, scalar restriction and [actual affine cohomology](../../../Cohomology/Affine/README.md). A finite-projective equivalence is not part of the selected finite-local-free global-generation result.

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
