/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Congruence
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Algebra homomorphisms from polynomial approximation

An exact solution of the relations of a native algebra presentation gives an
algebra homomorphism with the prescribed quotient-valued precision. A finite
polynomial approximation theorem therefore applies to every finitely presented
algebra, retaining equality of the original quotient-valued algebra maps.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u v w t

namespace Algebra.Presentation

variable {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
  {σ : Type w} {ι : Type t}

/-- Lift an actual solution of the presentation relations, retaining the exact
equality of the original quotient-valued algebra homomorphisms. -/
theorem exists_algHom_with_precision (P : Presentation R C σ ι)
    (I : Ideal R) (n : ℕ) (b : C →ₐ[R] AdicCompletion I R)
    (x : σ → R) (hx : ∀ i, eval x (P.relation i) = 0)
    (hprec : ∀ j, Ideal.Quotient.mk (I ^ n) (x j) =
      AdicCompletion.evalₐ I n (b (P.val j))) :
    ∃ a : C →ₐ[R] R,
      (Ideal.Quotient.mkₐ R (I ^ n)).comp a = (AdicCompletion.evalₐ I n).comp b := by
  have hker : RingHom.ker (aeval (R := R) P.val).toRingHom ≤
      RingHom.ker (aeval (R := R) x).toRingHom := by
    change RingHom.ker (aeval (R := R) P.val) ≤ RingHom.ker (aeval (R := R) x)
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx i
  let a : C →ₐ[R] R :=
    AlgHom.liftOfSurjective (aeval (R := R) P.val) P.aeval_val_surjective
      (aeval (R := R) x) hker
  have ha (j : σ) : a (P.val j) = x j := by
    simpa only [aeval_X] using
      AlgHom.liftOfSurjective_apply (aeval (R := R) P.val) P.aeval_val_surjective
        (aeval (R := R) x) hker (X j)
  refine ⟨a, (AlgHom.cancel_right P.aeval_val_surjective).mp ?_⟩
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, aeval_X, ha, Ideal.Quotient.mkₐ_eq_mk]
  exact hprec j

end Algebra.Presentation

namespace Algebra.FinitePresentation

variable {R : Type u} [CommRing R]

/-- Finite polynomial approximation supplies an algebra homomorphism from any
finitely presented algebra, with exact precision in the specified quotient. -/
theorem exists_algHom_with_precision_of_solver (I : Ideal R) (n : ℕ)
    (hsolve : ∀ (r s : ℕ) (F : Fin s → MvPolynomial (Fin r) R)
      (y : Fin r → AdicCompletion I R),
      (∀ i, eval₂ (algebraMap R (AdicCompletion I R)) y (F i) = 0) →
      ∃ x : Fin r → R, (∀ i, eval x (F i) = 0) ∧
        ∀ j, Ideal.Quotient.mk (I ^ n) (x j) = AdicCompletion.evalₐ I n (y j))
    (C : Type v) [CommRing C] [Algebra R C] [FinitePresentation R C]
    (b : C →ₐ[R] AdicCompletion I R) :
    ∃ a : C →ₐ[R] R,
      (Ideal.Quotient.mkₐ R (I ^ n)).comp a = (AdicCompletion.evalₐ I n).comp b := by
  let P := Algebra.Presentation.ofFinitePresentation R C
  have hy (i) : eval₂ (algebraMap R (AdicCompletion I R))
      (fun j => b (P.val j)) (P.relation i) = 0 := by
    rw [← aeval_def, ← comp_aeval_apply P.val b, P.aeval_val_relation, map_zero]
  obtain ⟨x, hx, hprec⟩ := hsolve _ _ P.relation (fun j => b (P.val j)) hy
  exact P.exists_algHom_with_precision I n b x hx hprec

/-- The same exact algebra-map comparison also controls every element of the
source algebra in the original completion, not only the chosen generators. -/
theorem exists_algHom_with_precision_and_error_of_solver (I : Ideal R) (hI : I.FG) (n : ℕ)
    (hsolve : ∀ (r s : ℕ) (F : Fin s → MvPolynomial (Fin r) R)
      (y : Fin r → AdicCompletion I R),
      (∀ i, eval₂ (algebraMap R (AdicCompletion I R)) y (F i) = 0) →
      ∃ x : Fin r → R, (∀ i, eval x (F i) = 0) ∧
        ∀ j, Ideal.Quotient.mk (I ^ n) (x j) = AdicCompletion.evalₐ I n (y j))
    (C : Type v) [CommRing C] [Algebra R C] [FinitePresentation R C]
    (b : C →ₐ[R] AdicCompletion I R) :
    ∃ a : C →ₐ[R] R,
      (Ideal.Quotient.mkₐ R (I ^ n)).comp a = (AdicCompletion.evalₐ I n).comp b ∧
      ∀ c, b c - algebraMap R (AdicCompletion I R) (a c) ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨a, ha⟩ := exists_algHom_with_precision_of_solver I n hsolve C b
  exact ⟨a, ha, (AdicCompletion.mkₐ_comp_eq_evalₐ_comp_iff I hI n b a).mp ha⟩

end Algebra.FinitePresentation
