/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PurelyInseparable.FixedField
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.CompleteLocalSurface
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite normalization of a complete normal local surface

The literal normalization of a complete Noetherian normal local domain of
dimension at most two is finite in every finite fraction-field extension.
The purely inseparable case is supplied by the actual height-one residue
layers and coefficient lifting. A finite normal hull then reduces the general
extension to a purely inseparable fixed field followed by a separable extension.
The original field embedding and coefficient action are retained throughout.

This does not cover a nonnormal complete base or establish a resolution.
-/

@[expose] public noncomputable section

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

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R] [Ring.KrullDimLE 2 R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L]

include K

/-- Normalization in every finite fraction-field extension is finite over the
original complete normal Noetherian local base of dimension at most two. -/
theorem finite_of_complete_local_normal_dimLE_two :
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
  let : Module.Finite R B :=
    finite_of_complete_local_normal_dimLE_two_of_isPurelyInseparable R K F
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
