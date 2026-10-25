/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.FiniteType

/-! # Generic finiteness of an actual affine quasi-finite algebra

Over a domain, the fraction-base change of a quasi-finite algebra is finite.
Clearing integral equations in the two localizations returns nonzero integral
multiples of the original elements. Finite generation then gives one nonzero
base element on whose principal open the actual base-changed algebra is finite.
Neither step requires a Noetherian or flatness hypothesis.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors
open Algebra TensorProduct

universe u v

namespace Algebra.QuasiFinite

variable (A : Type u) (B : Type v) [CommRing A] [IsDomain A]
  [CommRing B] [Algebra A B] [QuasiFinite A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Every original element of a quasi-finite algebra over a domain has a
nonzero base multiple that is integral over that original base. -/
theorem exists_nonzero_integral_smul (b : B) :
    ∃ a : A, a ≠ 0 ∧ IsIntegral A (a • b) := by
  let K := FractionRing A
  let T := K ⊗[A] B
  have : Module.Finite K T := Module.Finite.of_quasiFinite
  have hb : IsIntegral K (algebraMap B T b) := _root_.IsIntegral.of_finite K _
  obtain ⟨⟨a, ha⟩, hba⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization A⁰ (algebraMap B T b) hb
  have hba' : IsIntegral A (algebraMap B T (a • b)) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply] using hba
  obtain ⟨c, hc, hbc⟩ :=
    IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := T) A⁰ hba'
  exact ⟨c * a, mul_ne_zero (nonZeroDivisors.ne_zero hc)
    (nonZeroDivisors.ne_zero ha), by simpa only [mul_smul] using hbc⟩

/-- Quasi-finiteness over a domain supplies algebraicity of the original
algebra, including elements annihilated by a nonzero base scalar. -/
theorem isAlgebraic : Algebra.IsAlgebraic A B := by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, ha, hb⟩ := exists_nonzero_integral_smul A B b
  exact IsAlgebraic.of_smul_isIntegral (by simpa only [isNilpotent_iff_eq_zero] using ha) hb

end Algebra.QuasiFinite

namespace Algebra.IsAlgebraic

variable (A : Type u) (B : Type v) [CommRing A] [IsDomain A]
  [CommRing B] [Algebra A B] [Algebra.IsAlgebraic A B] [Algebra.FiniteType A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A finite-type algebraic algebra over a domain is finite after one
nonzero principal localization of the original base. The algebra in the
conclusion is the literal tensor-product base change. -/
theorem exists_nonzero_finite_baseChange_away :
    ∃ a : A, a ≠ 0 ∧ Module.Finite (Localization.Away a)
      (Localization.Away a ⊗[A] B) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  obtain ⟨a, ha, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples A s
  let R := Localization.Away a
  let T := R ⊗[A] B
  have haunit : IsUnit (algebraMap A R a) := IsLocalization.Away.algebraMap_isUnit a
  let ai : R := ↑(haunit.unit⁻¹)
  have hai : ai * algebraMap A R a = 1 := haunit.val_inv_mul
  have hgen (b : B) (hb : b ∈ s) : IsIntegral R (algebraMap B T b) := by
    have h : IsIntegral R (algebraMap B T (a • b)) :=
      ((hint b hb).map (IsScalarTower.toAlgHom A B T)).tower_top
    apply IsIntegral.of_mul_unit (r := ai)
      (y := algebraMap A T a)
    · rw [IsScalarTower.algebraMap_apply A R T, ← map_mul, hai, map_one]
    · simpa only [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply, mul_comm] using h
  have hnum (b : B) : IsIntegral R (algebraMap B T b) := by
    let C : Subalgebra A B :=
      ((integralClosure R T).restrictScalars A).comap (IsScalarTower.toAlgHom A B T)
    have hle : Algebra.adjoin A (s : Set B) ≤ C := by
      apply Algebra.adjoin_le
      intro b hb
      exact hgen b hb
    exact hle (by rw [hs]; trivial)
  have : Algebra.IsIntegral R T := by
    refine ⟨fun t => ?_⟩
    obtain ⟨b, d, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B (.powers a)) t
    rcases d with ⟨_, d, hd, rfl⟩
    have hdunit : IsUnit (algebraMap A R d) := IsLocalization.map_units R ⟨d, hd⟩
    let di : R := ↑(hdunit.unit⁻¹)
    have hdi : di * algebraMap A R d = 1 := hdunit.val_inv_mul
    apply IsIntegral.of_mul_unit (r := di) (y := algebraMap A T d)
    · rw [IsScalarTower.algebraMap_apply A R T, ← map_mul, hdi, map_one]
    · have hspec := IsLocalization.mk'_spec T b
        ⟨algebraMap A B d, Algebra.mem_algebraMapSubmonoid_of_mem ⟨d, hd⟩⟩
      rw [← IsScalarTower.algebraMap_apply A B T] at hspec
      rw [hspec]
      exact hnum b
  exact ⟨a, ha, Algebra.finite_iff_isIntegral_and_finiteType.mpr
    ⟨inferInstance, inferInstance⟩⟩

end Algebra.IsAlgebraic

namespace Algebra.QuasiFinite

variable (A : Type u) (B : Type v) [CommRing A] [IsDomain A]
  [CommRing B] [Algebra A B] [QuasiFinite A B] [Algebra.FiniteType A B]

/-- A quasi-finite finite-type affine algebra over a domain is genuinely
finite over a nonempty principal open of the original base. -/
theorem exists_nonzero_finite_baseChange_away :
    ∃ a : A, a ≠ 0 ∧ Module.Finite (Localization.Away a)
      (Localization.Away a ⊗[A] B) := by
  let : Algebra.IsAlgebraic A B := isAlgebraic A B
  exact Algebra.IsAlgebraic.exists_nonzero_finite_baseChange_away A B

end Algebra.QuasiFinite
