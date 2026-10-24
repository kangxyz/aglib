/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Flat base change and finite normalization

Flatness gives an actual injection from the original normalization after
base change into the literal upper normalization. Finiteness of the upper
normalization then descends by faithful flatness over a Noetherian upper
coefficient ring. Original total quotient rings and scalar maps are retained;
no locality, completeness, dimension, or domain hypotheses are imposed.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

universe u v w z

namespace integralClosure

section FlatBaseChange

variable (R : Type u) (S : Type v) (K : Type w) (Q : Type z)
  [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [CommRing Q] [Algebra S Q] [IsFractionRing S Q]

/-- Tensoring the original total quotient ring with a flat algebra maps
to the actual upper total quotient ring. Flatness verifies the unit
condition for every original denominator. -/
def flatFractionTensorMap : S ⊗[R] K →ₐ[S] Q := by
  apply IsLocalization.liftAlgHom
    (M := Algebra.algebraMapSubmonoid S R⁰) (f := Algebra.ofId S Q)
  intro y
  apply IsLocalization.map_units Q
    (⟨y.val, ?_⟩ : S⁰)
  rcases y.property with ⟨r, hr, heq⟩
  rw [← heq]
  apply mem_nonZeroDivisors_iff_left.mpr
  intro s hs
  have hreg : IsSMulRegular S r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  apply hreg
  simpa only [Algebra.smul_def, mul_zero] using hs

/-- The fraction tensor map extends the original upper coefficient map. -/
theorem flatFractionTensorMap_algebraMap (s : S) :
    flatFractionTensorMap R S K Q (algebraMap S (S ⊗[R] K) s) =
      algebraMap S Q s :=
  (flatFractionTensorMap R S K Q).commutes s

/-- On every original coefficient, the tensor map follows the actual
original ring map and then the upper total-quotient map. -/
@[simp]
theorem flatFractionTensorMap_one_tmul_algebraMap (r : R) :
    flatFractionTensorMap R S K Q (1 ⊗ₜ[R] algebraMap R K r) =
      algebraMap S Q (algebraMap R S r) := by
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] K),
    flatFractionTensorMap_algebraMap]

/-- The fraction tensor map is injective on the actual localization. -/
theorem flatFractionTensorMap_injective :
    Function.Injective (flatFractionTensorMap R S K Q) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Algebra.algebraMapSubmonoid S R⁰) (S ⊗[R] K)
    (flatFractionTensorMap R S K Q).toRingHom
  intro s hs
  change flatFractionTensorMap R S K Q (algebraMap S (S ⊗[R] K) s) = 0 at hs
  rw [flatFractionTensorMap_algebraMap] at hs
  have hs0 : s = 0 := by
    apply IsFractionRing.injective S Q
    simpa only [map_zero] using hs
  simp only [hs0, map_zero]

/-- The original normalization after flat scalar extension embeds into
the literal upper normalization, through the actual fraction tensor map. -/
def flatBaseChangeHom :
    S ⊗[R] integralClosure R K →ₐ[S] integralClosure S Q := by
  let f : S ⊗[R] integralClosure R K →ₐ[S] Q :=
    (flatFractionTensorMap R S K Q).comp
      (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val)
  let : Algebra.IsIntegral R (integralClosure R K) :=
    IsIntegralClosure.isIntegral_algebra R K
  exact f.codRestrict (integralClosure S Q) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := S) x).map f

/-- The normalization base-change map retains the original tensor
and the original ambient value of every integral element. -/
@[simp]
theorem flatBaseChangeHom_tmul (s : S) (x : integralClosure R K) :
    (flatBaseChangeHom R S K Q (s ⊗ₜ[R] x) : Q) =
      flatFractionTensorMap R S K Q (s ⊗ₜ[R] (x : K)) := rfl

/-- Flatness preserves the original normalization inclusion, and the
fraction tensor map preserves injectivity into the upper normalization. -/
theorem flatBaseChangeHom_injective :
    Function.Injective (flatBaseChangeHom R S K Q) := by
  have hj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R K).val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y h
  apply hj
  apply flatFractionTensorMap_injective R S K Q
  exact congrArg (fun b : integralClosure S Q ↦ (b : Q)) h

end FlatBaseChange

/-- Finiteness of the actual upper normalization descends through a
faithfully flat map when the upper coefficient ring is Noetherian.
All original total quotient rings and coefficient actions are retained. -/
theorem finite_of_faithfullyFlat
    (R : Type u) (S : Type v) (K : Type w) (Q : Type z)
    [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [IsNoetherianRing S]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [CommRing Q] [Algebra S Q] [IsFractionRing S Q]
    [Module.Finite S (integralClosure S Q)] :
    Module.Finite R (integralClosure R K) := by
  let : Module.Finite S (S ⊗[R] integralClosure R K) :=
    Module.Finite.of_injective (flatBaseChangeHom R S K Q).toLinearMap
      (flatBaseChangeHom_injective R S K Q)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

end integralClosure
