/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PurelyInseparable.FixedField
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite normalization from the purely inseparable case

`Aglib.RingTheory.IntegralClosure.NormalHull` reduces finite normalization in
every finite extension of a specified fraction field to finite normalization in
purely inseparable extensions. The original base is a Noetherian domain; it
need not be normal, local, complete or of bounded dimension.

The proof uses an actual finite normal hull, its full automorphism fixed field,
the trace-dual finiteness theorem over the normalization in that fixed field,
and the injective ambient map from the original extension. The purely
inseparable hypothesis tests fields in the same universe as the target field.
The current consumer is polynomial Japanese stability in `Aglib.RingTheory.Nagata`.
-/

@[expose] public noncomputable section

universe u v w

namespace integralClosure

private theorem finite_of_finite_integral_model
    (R B F E : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.IsIntegral R B]
    [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    [Field E] [Algebra F E] [Algebra B E] [Algebra R E]
    [IsScalarTower B F E] [IsScalarTower R B E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Module.Finite R (integralClosure R E) := by
  let : Module.Finite B (integralClosure B E) := IsIntegralClosure.finite B F E _
  let : Module.Finite R (integralClosure B E) :=
    Module.Finite.trans B (integralClosure B E)
  exact Module.Finite.equiv (equivOfIntegral R B E).toLinearEquiv

/-- Finite normalization in purely inseparable extensions of the supplied
fraction field implies finite normalization in every finite extension.
The test fields in `hpure` have the same universe as the target field `L`;
all coefficient maps and their scalar towers are retained. -/
theorem finite_of_finite_purelyInseparable
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (hpure : ∀ (F : Type w) [Field F] [Algebra K F] [Algebra R F]
      [IsScalarTower R K F] [FiniteDimensional K F] [IsPurelyInseparable K F],
      Module.Finite R (integralClosure R F)) :
    Module.Finite R (integralClosure R L) := by
  let Ω := AlgebraicClosure L
  let : IsAlgClosure K Ω := IsAlgClosure.ofAlgebraic K L Ω
  let M := IntermediateField.normalClosure K L Ω
  let : IsScalarTower R M Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R L M := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    apply (algebraMap M Ω).injective
    change algebraMap R Ω r = algebraMap L Ω (algebraMap R L r)
    exact IsScalarTower.algebraMap_apply R L Ω r
  let H := (⊤ : Subgroup (M ≃ₐ[K] M))
  let : Fintype (M ≃ₐ[K] M) := AlgEquiv.fintype K M
  let F := IntermediateField.fixedField H
  let : IsPurelyInseparable K F :=
    IntermediateField.isPurelyInseparable_fixedField_top K M
  let : IsGalois F M := IsGalois.of_fixed_field M H
  let : IsScalarTower R F M := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure R F
  let : Module.Finite R B := hpure F
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : IsFractionRing B F := isFractionRing_of_finite_extension K F
  let : IsIntegrallyClosed B := isIntegrallyClosedOfFiniteExtension K
  let : Algebra.IsIntegral R B := IsIntegralClosure.isIntegral_algebra R F
  let : Module.Finite R (integralClosure R M) :=
    finite_of_finite_integral_model R B F M
  let f : L →ₐ[R] M := IsScalarTower.toAlgHom R L M
  let g : integralClosure R L →ₐ[R] integralClosure R M := f.mapIntegralClosure
  apply Module.Finite.of_injective g.toLinearMap
  intro x y h
  apply Subtype.ext
  apply f.injective
  exact congrArg Subtype.val h

end integralClosure
