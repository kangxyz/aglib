/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Completion of an actual maximal localization

The native quotient isomorphisms at every positive or zero power are compatible
with transition maps, so they induce an actual algebra equivalence of completions.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing IsLocalization.AtPrime

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] [IsLocalRing S]

/-- Native localization quotient equivalences commute with their actual transitions. -/
theorem localizationQuotient_factor {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ p ^ n) :
    equivQuotMaximalIdealPow p S m (Ideal.Quotient.factorPow p hmn x) =
      Ideal.Quotient.factorPow (maximalIdeal S) hmn (equivQuotMaximalIdealPow p S n x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Extension of the actual localization map to the two completions. -/
def localizationTo : AdicCompletion p R →ₐ[R] AdicCompletion (maximalIdeal S) S :=
  liftAlgHom (maximalIdeal S)
    (fun n => (equivQuotMaximalIdealPow p S n).toAlgHom.comp (evalₐ p n))
    (fun {m n} hmn => by
      apply AlgHom.ext
      intro x
      change Ideal.Quotient.factorPow (maximalIdeal S) hmn
          (equivQuotMaximalIdealPow p S n (evalₐ p n x)) =
        equivQuotMaximalIdealPow p S m (evalₐ p m x)
      rw [← localizationQuotient_factor]
      exact congrArg (equivQuotMaximalIdealPow p S m) (factor_evalₐ p hmn x))

@[simp]
theorem eval_localizationTo (n : ℕ) (x : AdicCompletion p R) :
    evalₐ (maximalIdeal S) n (localizationTo p S x) =
      equivQuotMaximalIdealPow p S n (evalₐ p n x) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The inverse is built from the actual inverse localization quotient maps. -/
def localizationFrom : AdicCompletion (maximalIdeal S) S →ₐ[R] AdicCompletion p R :=
  liftAlgHom p
    (fun n => (equivQuotMaximalIdealPow p S n).symm.toAlgHom.comp
      ((evalₐ (maximalIdeal S) n).restrictScalars R))
    (fun {m n} hmn => by
      apply AlgHom.ext
      intro x
      apply (equivQuotMaximalIdealPow p S m).injective
      change equivQuotMaximalIdealPow p S m
          (Ideal.Quotient.factorPow p hmn
            ((equivQuotMaximalIdealPow p S n).symm (evalₐ (maximalIdeal S) n x))) =
        equivQuotMaximalIdealPow p S m
          ((equivQuotMaximalIdealPow p S m).symm (evalₐ (maximalIdeal S) m x))
      rw [localizationQuotient_factor, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact factor_evalₐ (maximalIdeal S) hmn x)

@[simp]
theorem eval_localizationFrom (n : ℕ) (x : AdicCompletion (maximalIdeal S) S) :
    evalₐ p n (localizationFrom p S x) =
      (equivQuotMaximalIdealPow p S n).symm (evalₐ (maximalIdeal S) n x) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- Completing at an original maximal ideal is the same as completing its
actual local ring. The equivalence preserves the original ring map. -/
def localizationAlgEquiv :
    AdicCompletion p R ≃ₐ[R] AdicCompletion (maximalIdeal S) S :=
  AlgEquiv.ofAlgHom (localizationTo p S) (localizationFrom p S)
    (by
      apply AlgHom.ext
      intro x
      apply ext_evalₐ
      intro n
      simp only [AlgHom.comp_apply, AlgHom.id_apply, eval_localizationTo,
        eval_localizationFrom, AlgEquiv.apply_symm_apply])
    (by
      apply AlgHom.ext
      intro x
      apply ext_evalₐ
      intro n
      simp only [AlgHom.comp_apply, AlgHom.id_apply, eval_localizationTo,
        eval_localizationFrom, AlgEquiv.symm_apply_apply])

theorem localizationAlgEquiv_algebraMap (r : R) :
    localizationAlgEquiv p S (algebraMap R (AdicCompletion p R) r) =
      algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap R S r) :=
  (localizationAlgEquiv p S).commutes r

end AdicCompletion
