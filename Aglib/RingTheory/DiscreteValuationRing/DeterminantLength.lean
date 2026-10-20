/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.Norm.Basic

/-!
# Determinant valuations and actual cokernel lengths over a DVR

This is an algebraic component for `NormDegree.FiniteMorphismNormOrder`.
For an injective endomorphism of a finite free module over a discrete
valuation ring, its determinant valuation equals the length of its actual
cokernel. The proof uses Smith normal form and the lengths of quotients by
powers of the maximal ideal. Specializing to multiplication identifies the
determinant with `Algebra.norm`; neither perfectness nor separability is used.

This file does not construct the full inverse image of a scheme stalk, nor
identify its maximal ideals with the closed fibre of a finite morphism.
-/

@[expose] public section




noncomputable section
open Module IsDiscreteValuationRing
namespace IsDiscreteValuationRing.FiniteNorm

universe u v w
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual quotient by a nonzero principal ideal has the DVR valuation as length. -/
theorem length_quotient_span_eq_addVal (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = addVal R a := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
    length_quotient_pow_maximalIdeal]

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι]

/-- Smith normal form computes the length of an actual full-rank quotient. -/
theorem length_quotient_eq_sum_addVal (b : Basis ι R M) (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Module.length R (M ⧸ N) = ∑ i, addVal R (N.smithNormalFormCoeffs b h i) := by
  rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact length_quotient_span_eq_addVal _ (N.smithNormalFormCoeffs_ne_zero b h i)

omit [Fintype ι] in
theorem addVal_prod (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert hi, Finset.sum_insert hi, ih]

omit [Fintype ι] in
/-- The determinant valuation of an injective endomorphism is its cokernel length. -/
theorem length_cokernel_eq_addVal_det [Finite ι] (b : Basis ι R M) (φ : M →ₗ[R] M)
    (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range φ) = addVal R (LinearMap.det φ) := by
  classical
  let := Fintype.ofFinite ι
  let N := LinearMap.range φ
  have hr : Module.finrank R N = Module.finrank R M := φ.finrank_range_of_inj hφ
  let c := N.smithNormalFormTopBasis b hr
  let d := N.smithNormalFormBotBasis b hr
  let a := N.smithNormalFormCoeffs b hr
  let e : M ≃ₗ[R] N := c.equiv d (Equiv.refl _)
  let ψ : M →ₗ[R] M := N.subtype.comp e.toLinearMap
  have hψ : ∀ i, ψ (c i) = a i • c i := by
    intro i
    simpa only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Basis.equiv_apply,
      Submodule.subtype_apply, Equiv.refl_apply, c, d, a]
      using N.smithNormalFormBotBasis_def b hr i
  have hmatrix : LinearMap.toMatrix c c ψ = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, hψ]
    · simp [LinearMap.toMatrix_apply, hψ, hij]
  have hdet : LinearMap.det ψ = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix c, hmatrix, Matrix.det_diagonal]
  have hassoc : Associated (LinearMap.det φ) (LinearMap.det ψ) := by
    have hcomp : N.subtype.comp (LinearEquiv.ofInjective φ hφ).toLinearMap = φ := by
      ext x
      rfl
    have h := LinearMap.associated_det_comp_equiv N.subtype
      (LinearEquiv.ofInjective φ hφ) e
    rw [hcomp] at h
    exact h
  rw [length_quotient_eq_sum_addVal b N hr,
    (addVal_eq_iff_associated _ _).mpr hassoc, hdet]
  exact (addVal_prod Finset.univ a).symm

/-- A basis-free formulation for a finite free module. -/
theorem length_cokernel_eq_addVal_det_of_finite_free [Module.Free R M]
    [Module.Finite R M] (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range φ) = addVal R (LinearMap.det φ) :=
  length_cokernel_eq_addVal_det (Module.Free.chooseBasis R M) φ hφ

variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] in
/-- Multiplication has the actual principal ideal as its range after restricting scalars. -/
theorem range_lmul_eq_restrictScalars_span (a : S) :
    LinearMap.range (Algebra.lmul R S a) = (Ideal.span ({a} : Set S)).restrictScalars R := by
  ext x
  change (∃ b, a * b = x) ↔ x ∈ Ideal.span ({a} : Set S)
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩

/-- The determinant norm of a finite free domain algebra measures the principal quotient. -/
theorem length_quotient_span_eq_addVal_norm [Module.Free R S] [Module.Finite R S]
    (a : S) (ha : a ≠ 0) :
    Module.length R (S ⧸ (Ideal.span ({a} : Set S)).restrictScalars R) =
      addVal R (Algebra.norm R a) := by
  rw [← range_lmul_eq_restrictScalars_span]
  exact length_cokernel_eq_addVal_det_of_finite_free (Algebra.lmul R S a)
    (mul_right_injective₀ ha)

/-- The principal quotient is of finite length over the base DVR. -/
theorem quotient_span_finiteLength_of_finite_free [Module.Free R S] [Module.Finite R S]
    (a : S) (ha : a ≠ 0) :
    IsFiniteLength R (S ⧸ (Ideal.span ({a} : Set S)).restrictScalars R) := by
  rw [← Module.length_ne_top_iff, length_quotient_span_eq_addVal_norm a ha,
    ne_eq, addVal_eq_top_iff]
  exact Algebra.norm_ne_zero_iff.mpr ha

end IsDiscreteValuationRing.FiniteNorm

/- Migration source: R5Lab/Aglib/RingTheory/DiscreteValuationRing/DeterminantLength.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 1736babed05ca7e07c85e168454b713eb426618a28e8ef0b660275ce1f2f7e0a.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
