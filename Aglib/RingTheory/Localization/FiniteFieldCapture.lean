/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.FiniteIntegralCaptureAway
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Localization.Integer

/-! # Finite coefficient capture retaining the original extension field

A finite basis is captured together with the requested coefficients. Clearing
its original fraction-field coefficients then proves that the same ambient
extension is the fraction field of the actual captured localization.
-/

@[expose] public noncomputable section

open scoped BigOperators nonZeroDivisors

namespace IsFractionRing

universe u v w t

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type w} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- An actual injective coefficient algebra containing a finite K-basis of L
has the original L as its fraction field. The fractions are constructed by
clearing the coefficients of that basis, not by choosing another field. -/
theorem of_basis_mem_range
    {A : Type t} [CommRing A] [Algebra R A] (f : A →ₐ[R] L)
    (hf : Function.Injective f) {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) (hb : ∀ i, b i ∈ f.range) :
    letI : Algebra A L := f.toRingHom.toAlgebra
    IsFractionRing A L := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Algebra A L := f.toRingHom.toAlgebra
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hf
  apply IsFractionRing.of_field
  intro z
  choose y hy using hb
  change ∀ i, f (y i) = b i at hy
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun i => b.repr z i)
  choose c hc using hd
  have hdL : algebraMap R L (d : R) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp d.property
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [map_zero] using h
  have hcoeff (i : ι) : algebraMap R L (c i) =
      algebraMap R L (d : R) * algebraMap K L (b.repr z i) := by
    rw [IsScalarTower.algebraMap_apply R K L, hc i]
    simp only [Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply R K L]
  have hsum : f (∑ i, c i • y i) = algebraMap R L (d : R) * z := by
    have hterm (i : ι) : f (c i • y i) =
        algebraMap R L (d : R) * (algebraMap K L (b.repr z i) * b i) := by
      rw [Algebra.smul_def, map_mul, f.commutes, hy, hcoeff, mul_assoc]
    rw [map_sum]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    congr 1
    simpa only [Algebra.smul_def] using b.sum_repr z
  refine ⟨∑ i, c i • y i, algebraMap R A (d : R), ?_⟩
  change z = f (∑ i, c i • y i) / f (algebraMap R A (d : R))
  rw [f.commutes, hsum, mul_div_cancel_left₀ _ hdL]

variable [Module.Finite K L]

include K in
/-- Capture the requested finite coefficients and a basis in the existing
finite-subalgebra construction. Its original localization embeds in L and has
L itself as fraction field; no normalization finiteness is assumed. -/
theorem exists_finiteSubalgebra_away_capture_fractionField (s : Finset L) :
    ∃ r : R, r ≠ 0 ∧ ∃ hr : algebraMap R L r ≠ 0,
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        Function.Injective (finiteSubalgebraAwayMap B r hr) ∧
        (∀ x ∈ s, x ∈ (finiteSubalgebraAwayMap B r hr).range) ∧
        (letI : Algebra (Localization.Away (algebraMap R B r)) L :=
          (finiteSubalgebraAwayMap B r hr).toRingHom.toAlgebra
         IsFractionRing (Localization.Away (algebraMap R B r)) L) := by
  classical
  let b := Module.finBasis K L
  obtain ⟨r, hr, hrL, B, hB, hinj, hmem⟩ :=
    exists_finiteSubalgebra_away_capture R K (s ∪ Finset.univ.image b)
  refine ⟨r, hr, hrL, B, hB, hinj, (fun x hx => hmem x (Finset.mem_union_left _ hx)), ?_⟩
  exact of_basis_mem_range R K (finiteSubalgebraAwayMap B r hrL) hinj b
    (fun i => hmem (b i) (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩)))

include K in
/-- A finitely generated coefficient subalgebra factors through the original
finite capture localization. The factor map, its literal coefficient equation,
and the original extension field as fraction field are constructed together. -/
theorem exists_finiteSubalgebra_away_factor_fractionField
    (A : Subalgebra R L) (hA : A.FG) :
    ∃ r : R, r ≠ 0 ∧ ∃ hr : algebraMap R L r ≠ 0,
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        Function.Injective (finiteSubalgebraAwayMap B r hr) ∧
        (∃ ψ : A →ₐ[R] Localization.Away (algebraMap R B r),
          (finiteSubalgebraAwayMap B r hr).comp ψ = A.val) ∧
        (letI : Algebra (Localization.Away (algebraMap R B r)) L :=
          (finiteSubalgebraAwayMap B r hr).toRingHom.toAlgebra
         IsFractionRing (Localization.Away (algebraMap R B r)) L) := by
  classical
  obtain ⟨s, hs⟩ := hA
  obtain ⟨r, hr, hrL, B, hB, hinj, hmem, hfrac⟩ :=
    exists_finiteSubalgebra_away_capture_fractionField R K s
  let f := finiteSubalgebraAwayMap B r hrL
  have hle : A ≤ f.range := by
    rw [← hs]
    exact Algebra.adjoin_le_iff.mpr (fun x hx => hmem x hx)
  let ψ : A →ₐ[R] Localization.Away (algebraMap R B r) :=
    (AlgEquiv.ofInjective f hinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hψ : f.comp ψ = A.val := by
    ext x
    exact congrArg Subtype.val ((AlgEquiv.ofInjective f hinj).apply_symm_apply
      (Subalgebra.inclusion hle x))
  exact ⟨r, hr, hrL, B, hB, hinj, ⟨ψ, hψ⟩, hfrac⟩

end IsFractionRing
