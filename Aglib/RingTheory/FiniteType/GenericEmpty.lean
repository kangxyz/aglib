/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Spreading the emptiness of an original finite-type algebra

An empty geometric generic fibre of a finite-type algebra is already empty
on one nonzero principal open of the original domain. The conclusion is an
actual scalar vanishing in the original algebra, not an auxiliary model.
This is the emptiness step in Stacks Project, Tag 0557; no Noetherian or
perfectness assumption is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace Algebra.FiniteType

/-- A nontrivial finite-type algebra over a field has a point in every
algebraically closed extension of that field. -/
theorem nonempty_algHom_to_isAlgClosed
    (K B Ω : Type*) [Field K] [CommRing B] [Nontrivial B] [Algebra K B]
    [Algebra.FiniteType K B] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    Nonempty (B →ₐ[K] Ω) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[K] Ω).comp (Ideal.Quotient.mkₐ K m)⟩

/-- If the original finite-type algebra has no geometric generic point,
a nonzero scalar of the original domain already vanishes in that algebra. -/
theorem exists_ne_zero_algebraMap_eq_zero_of_isEmpty_algHom
    (R K B Ω : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    (h : IsEmpty (B →ₐ[R] Ω)) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R B r = 0 := by
  have hzero : (1 : K ⊗[R] B) = 0 := by
    by_contra hne
    let : Nontrivial (K ⊗[R] B) := ⟨⟨1, 0, hne⟩⟩
    obtain ⟨g⟩ := nonempty_algHom_to_isAlgClosed K (K ⊗[R] B) Ω
    exact h.false ((g.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have htensor : TensorProduct.mk R K B 1 (1 : B) = 0 := by
    simpa only [TensorProduct.mk_apply, Algebra.TensorProduct.one_def] using hzero
  obtain ⟨r, hr⟩ :=
    (IsLocalizedModule.eq_zero_iff R⁰ (TensorProduct.mk R K B 1)).mp htensor
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp r.property, ?_⟩
  simpa only [Submonoid.smul_def, Algebra.smul_def, mul_one] using hr

/-- The same scalar excludes every field-valued point of the original algebra
whose original base map does not kill that scalar. -/
theorem exists_ne_zero_forall_no_field_point_of_isEmpty_algHom
    (R K B Ω : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    (h : IsEmpty (B →ₐ[R] Ω)) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type*) [Field L] (φ : R →+* L), φ r ≠ 0 →
      ¬ ∃ ψ : B →+* L, ψ.comp (algebraMap R B) = φ := by
  obtain ⟨r, hr, hzero⟩ :=
    exists_ne_zero_algebraMap_eq_zero_of_isEmpty_algHom R K B Ω h
  refine ⟨r, hr, fun L _ φ hφ ⟨ψ, hψ⟩ => hφ ?_⟩
  rw [← hψ, RingHom.comp_apply, hzero, map_zero]

end Algebra.FiniteType
