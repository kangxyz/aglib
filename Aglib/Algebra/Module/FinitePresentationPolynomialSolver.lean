/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.PolynomialPresentationCoordinates
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Basic.Finite.Sum

/-! # Encoding polynomial equations through a finite module presentation

A polynomial system over a finite algebra is converted to a genuine finite
polynomial system over the base ring. Extra variables encode the relations of
the module presentation, rather than incorrectly treating its generators as a
basis. The exact formal solution supplies these relation witnesses by right
exactness of tensor product.
-/

@[expose] public noncomputable section

open TensorProduct MvPolynomial
open scoped BigOperators

namespace Module.FinitePresentation

universe u v w t
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {T : Type t} [CommRing T] [Algebra R T]
variable {d r : ℕ} (f : (Fin d → R) →ₗ[R] A) (hf : Function.Surjective f)
variable (g : (Fin r → R) →ₗ[R] (Fin d → R)) (hgf : Function.Exact g f)
variable {σ : Type v} {ι : Type w}

include hf g hgf in
/-- Genuine finite polynomial descent, retaining the precision of every
coordinate supplied by the base solver. -/
theorem exists_solution_coordinates_of_solver [Finite σ] [Finite ι]
    (K : Ideal T)
    (hsolve : ∀ {τ : Type (max v w)} [Finite τ] {ε : Type w} [Finite ε]
      (E : ε → MvPolynomial τ R) (t : τ → T),
      (∀ i, eval₂ (algebraMap R T) t (E i) = 0) →
      ∃ b : τ → R, (∀ i, eval b (E i) = 0) ∧
        ∀ j, algebraMap R T (b j) - t j ∈ K)
    (F : ι → MvPolynomial σ A) (z : σ → Fin d → T)
    (hz : ∀ i, eval₂
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
      (fun j ↦ tensorCoordinates T f (z j)) (F i) = 0) :
    ∃ b : σ → Fin d → R,
      (∀ i, eval (fun j ↦ f (b j)) (F i) = 0) ∧
      ∀ j a, algebraMap R T (b j a) - z j a ∈ K := by
  classical
  let ρ := σ × Fin d
  let τ := Sum ρ (ι × Fin r)
  let : Finite τ := inferInstanceAs (Finite (Sum (σ × Fin d) (ι × Fin r)))
  let Q : σ → MvPolynomial ρ A := fun j ↦
    ∑ a, C (f (Pi.single a 1)) * X (j, a)
  let P : ι → MvPolynomial ρ A := fun i ↦ bind₁ Q (F i)
  let C : ι → Fin d → MvPolynomial ρ R := fun i ↦ polynomialCoordinates f hf (P i)
  let z₀ : ρ → T := fun p ↦ z p.1 p.2
  have hQ (j : σ) : eval₂
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
      (fun p ↦ z₀ p ⊗ₜ[R] (1 : A)) (Q j) = tensorCoordinates T f (z j) := by
    rw [tensorCoordinates_apply]
    simp [Q, z₀, Algebra.TensorProduct.tmul_mul_tmul]
  have hP (i : ι) : tensorCoordinates T f
      (fun a ↦ eval₂ (algebraMap R T) z₀ (C i a)) = 0 := by
    rw [tensorCoordinates_eval₂ f hf]
    change eval₂Hom _ _ (bind₁ Q (F i)) = 0
    rw [eval₂Hom_bind₁]
    simpa only [coe_eval₂Hom, hQ] using hz i
  choose w hw using fun i ↦
    (tensorCoordinates_eq_zero_iff T f g hf hgf _).mp (hP i)
  let t₀ : τ → T := Sum.elim z₀ (fun p ↦ w p.1 p.2)
  let E : (ι × Fin d) → MvPolynomial τ R := fun p ↦
    rename Sum.inl (C p.1 p.2) -
      ∑ b, MvPolynomial.C (g (Pi.single b 1) p.2) * X (Sum.inr (p.1, b))
  have hE (p : ι × Fin d) : eval₂ (algebraMap R T) t₀ (E p) = 0 := by
    have h := congrFun (hw p.1) p.2
    rw [tensorRelations_apply] at h
    simp only [E, eval₂_sub, eval₂_rename, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X]
    change eval₂ (algebraMap R T) z₀ (C p.1 p.2) -
      ∑ b, algebraMap R T (g (Pi.single b 1) p.2) * w p.1 b = 0
    rw [← h]
    simp only [Algebra.smul_def, sub_self]
  obtain ⟨b, hb, hclose⟩ := hsolve E t₀ hE
  let b₀ : ρ → R := fun p ↦ b (Sum.inl p)
  let b₁ : ι → Fin r → R := fun i a ↦ b (Sum.inr (i, a))
  have hrel (i : ι) : (fun a ↦ eval b₀ (C i a)) = g (b₁ i) := by
    ext a
    have h := hb (i, a)
    simp only [E, eval_sub, eval_rename, eval_sum, eval_mul, eval_C, eval_X,
      sub_eq_zero] at h
    rw [pi_eq_sum_univ' (b₁ i)]
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      b₀, b₁, Function.comp_def, mul_comm] using h
  refine ⟨fun j a ↦ b₀ (j, a), ?_, fun j a ↦ hclose (Sum.inl (j, a))⟩
  intro i
  have hcoord : eval₂ (RingHom.id A)
      (fun p ↦ algebraMap R A (b₀ p)) (P i) =
      f (fun a ↦ eval b₀ (C i a)) := by
    change eval₂ (AlgHom.id R A).toRingHom
      (fun p ↦ algebraMap R A (b₀ p)) (P i) = _
    rw [eval₂_polynomialCoordinates f hf (AlgHom.id R A)]
    rw [presentation_apply]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Algebra.smul_def]
    have he := eval₂_comp (algebraMap R A) b₀ (C i a)
    simpa only [AlgHom.id_apply, RingHom.id_comp, Function.comp_def, mul_comm] using
      congrArg (fun t ↦ t * f (Pi.single a 1)) he.symm
  rw [hrel, hgf.apply_apply_eq_zero] at hcoord
  change eval₂Hom (RingHom.id A) _ (bind₁ Q (F i)) = 0 at hcoord
  rw [eval₂Hom_bind₁] at hcoord
  have hQbase (j : σ) : eval₂ (RingHom.id A)
      (fun p ↦ algebraMap R A (b₀ p)) (Q j) = f (fun a ↦ b₀ (j, a)) := by
    rw [presentation_apply]
    simp [Q, Algebra.smul_def, mul_comm]
  simpa only [coe_eval₂Hom, hQbase, eval₂_id] using hcoord

end Module.FinitePresentation
