/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.LocalRigidity
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Encoding coefficients from an etale presentation

A polynomial system over a finitely presented etale algebra is encoded over
its base by adjoining the presentation generators and relations. The same
encoded system works in every local target. Near a fixed stage point, its
auxiliary coordinates are forced to equal that point exactly. This does not
assert that the enlarged system is square or preserves a Jacobian minor.
-/

@[expose] public section

noncomputable section

open MvPolynomial IsLocalRing

universe u v w₁ w₂ w₃ w₄ t

namespace Algebra.Presentation

private lemma eval₂_sumAlgEquiv_symm
    {R T σ ν : Type*} [CommRing R] [CommRing T]
    (α : R →+* T) (y : σ → T) (z : ν → T)
    (H : MvPolynomial σ (MvPolynomial ν R)) :
    eval₂ α (Sum.elim y z) ((sumAlgEquiv R σ ν).symm H) =
      eval₂ (eval₂Hom α z) y H := by
  have h : (eval₂Hom (eval₂Hom α z) y).comp
      (sumAlgEquiv R σ ν).toRingHom = eval₂Hom α (Sum.elim y z) := by
    ext r
    · simp
    · cases r <;> simp
  have hh := RingHom.congr_fun h ((sumAlgEquiv R σ ν).symm H)
  simpa using hh.symm

/-- Encode a polynomial system over an etale algebra using a chosen presentation.
The encoded system is finite when its equation, unknown, generator and relation
index types are finite. Every local target uses the same equations and original
coefficient map; residue agreement fixes all auxiliary coordinates exactly. -/
theorem exists_polynomial_system_over_base
    {R : Type u} {B : Type v} {σ : Type w₁} {ι : Type w₂}
    {ν : Type w₃} {ρ : Type w₄}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (P : Presentation R B ν ρ) (G : ι → MvPolynomial σ B) :
    ∃ E : (ι ⊕ ρ) → MvPolynomial (σ ⊕ ν) R,
      ∀ (T : Type t) [CommRing T] [Algebra R T] [IsLocalRing T]
        (f : B →ₐ[R] T) (y : σ → T),
      ((∀ k, eval₂ (algebraMap R T) (Sum.elim y (fun j => f (P.val j)))
          (E k) = 0) ↔ ∀ i, eval₂ f.toRingHom y (G i) = 0) ∧
      (∀ z : ν → T,
        (∀ k, eval₂ (algebraMap R T) (Sum.elim y z) (E k) = 0) →
        (∀ j, z j - f (P.val j) ∈ maximalIdeal T) →
        (∀ j, z j = f (P.val j)) ∧ ∀ i, eval₂ f.toRingHom y (G i) = 0) := by
  classical
  have hG (i : ι) : ∃ H : MvPolynomial σ (MvPolynomial ν R),
      map (aeval P.val).toRingHom H = G i :=
    MvPolynomial.map_surjective (aeval (R := R) P.val).toRingHom
      P.aeval_val_surjective (G i)
  choose H hH using hG
  let E : (ι ⊕ ρ) → MvPolynomial (σ ⊕ ν) R :=
    Sum.elim (fun i => (sumAlgEquiv R σ ν).symm (H i))
      (fun j => rename Sum.inr (P.relation j))
  refine ⟨E, ?_⟩
  intro T _ _ _ f y
  have hcoeff : f.toRingHom.comp (aeval P.val).toRingHom =
      eval₂Hom (algebraMap R T) (fun j => f (P.val j)) := by
    ext r <;> simp
  have hmain (i : ι) :
      eval₂ (algebraMap R T) (Sum.elim y (fun j => f (P.val j))) (E (.inl i)) =
        eval₂ f.toRingHom y (G i) := by
    change eval₂ (algebraMap R T) (Sum.elim y (fun j => f (P.val j)))
      ((sumAlgEquiv R σ ν).symm (H i)) = _
    rw [eval₂_sumAlgEquiv_symm, ← hH i, eval₂_map, hcoeff]
  have hrelations (z : ν → T) (j : ρ) :
      eval₂ (algebraMap R T) (Sum.elim y z) (E (.inr j)) =
        aeval z (P.relation j) := by
    change eval₂ (algebraMap R T) (Sum.elim y z)
      (rename Sum.inr (P.relation j)) = _
    rw [eval₂_rename]
    rfl
  have hfixed (j : ρ) : aeval (fun j => f (P.val j)) (P.relation j) = 0 := by
    change eval₂Hom (algebraMap R T) (fun j => f (P.val j)) (P.relation j) = 0
    rw [← hcoeff]
    change f (aeval P.val (P.relation j)) = 0
    rw [P.aeval_val_relation, map_zero]
  constructor
  · constructor
    · intro h i
      exact (hmain i).symm.trans (h (.inl i))
    · intro h k
      cases k with
      | inl i => exact (hmain i).trans (h i)
      | inr j => exact (hrelations _ j).trans (hfixed j)
  · intro z hz hclose
    have hrel (j : ρ) : aeval z (P.relation j) = 0 :=
      (hrelations z j).symm.trans (hz (.inr j))
    have heq := P.eq_point_of_relation_eq_zero_of_sub_mem_maximalIdeal f z hrel hclose
    refine ⟨heq, ?_⟩
    have hzfun : z = fun j => f (P.val j) := funext heq
    subst z
    intro i
    exact (hmain i).symm.trans (hz (.inl i))

end Algebra.Presentation
