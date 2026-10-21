/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationQuotientSystem
public import Aglib.RingTheory.AdicCompletion.Transition

/-!
# Completion of the actual henselization

The original maps on all infinitesimal quotients induce an algebra equivalence
between the native maximal-ideal completions of a local ring and its actual
henselization. Both maps are native completion lifts and their inverse laws
are checked on every quotient coordinate. No Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The forward quotient-coordinate family is compatible with the native transitions. -/
theorem completionMap_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal (Henselization R)) hmn)).comp
        ((quotientMaximalIdealPowMap R n).comp
          (AdicCompletion.evalₐ (maximalIdeal R) n)) =
      (quotientMaximalIdealPowMap R m).comp
        (AdicCompletion.evalₐ (maximalIdeal R) m) := by
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.factorPow (maximalIdeal (Henselization R)) hmn
      (quotientMaximalIdealPowMap R n (AdicCompletion.evalₐ (maximalIdeal R) n x)) =
    quotientMaximalIdealPowMap R m (AdicCompletion.evalₐ (maximalIdeal R) m x)
  have h := RingHom.congr_fun (quotientMaximalIdealPowMap_factorPow R hmn)
    (AdicCompletion.evalₐ (maximalIdeal R) n x)
  exact h.trans (congrArg (quotientMaximalIdealPowMap R m)
    (AdicCompletion.factorPow_evalₐ (maximalIdeal R) hmn x))

/-- The map on completions induced by the original base algebra map. -/
def completionMap :
    AdicCompletion (maximalIdeal R) R →ₐ[R]
      AdicCompletion (maximalIdeal (Henselization R)) (Henselization R) :=
  AdicCompletion.liftAlgHom (maximalIdeal (Henselization R))
    (fun n => (quotientMaximalIdealPowMap R n).comp
      (AdicCompletion.evalₐ (maximalIdeal R) n)) (completionMap_compatible R)

/-- The inverse quotient-coordinate family respects the native transitions. -/
theorem completionMapInv_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (I := maximalIdeal R) hmn)).comp
        ((quotientMaximalIdealPowEquivAll R n).symm.toAlgHom.comp
          ((AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n).restrictScalars R)) =
      (quotientMaximalIdealPowEquivAll R m).symm.toAlgHom.comp
        ((AdicCompletion.evalₐ (maximalIdeal (Henselization R)) m).restrictScalars R) := by
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.factorPow (maximalIdeal R) hmn
      ((quotientMaximalIdealPowEquivAll R n).symm
        (AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n x)) =
    (quotientMaximalIdealPowEquivAll R m).symm
      (AdicCompletion.evalₐ (maximalIdeal (Henselization R)) m x)
  rw [← quotientMaximalIdealPowEquivAll_symm_factorPow, AdicCompletion.factorPow_evalₐ]

/-- The inverse completion map, obtained from the actual inverse quotient maps. -/
def completionMapInv :
    AdicCompletion (maximalIdeal (Henselization R)) (Henselization R) →ₐ[R]
      AdicCompletion (maximalIdeal R) R :=
  AdicCompletion.liftAlgHom (maximalIdeal R)
    (fun n => (quotientMaximalIdealPowEquivAll R n).symm.toAlgHom.comp
      ((AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n).restrictScalars R))
    (completionMapInv_compatible R)

@[simp] theorem eval_completionMap (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) :
    AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n (completionMap R x) =
      quotientMaximalIdealPowMap R n (AdicCompletion.evalₐ (maximalIdeal R) n x) := by
  unfold completionMap
  exact AdicCompletion.evalₐ_liftAlgHom _ _ (completionMap_compatible R) n x

@[simp] theorem eval_completionMapInv (n : ℕ)
    (x : AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)) :
    AdicCompletion.evalₐ (maximalIdeal R) n (completionMapInv R x) =
      (quotientMaximalIdealPowEquivAll R n).symm
        (AdicCompletion.evalₐ (maximalIdeal (Henselization R)) n x) := by
  unfold completionMapInv
  exact AdicCompletion.evalₐ_liftAlgHom _ _ (completionMapInv_compatible R) n x

/-- The inverse law is verified on the native evaluations at all ideal powers. -/
theorem completionMapInv_completionMap (x : AdicCompletion (maximalIdeal R) R) :
    completionMapInv R (completionMap R x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_completionMapInv, eval_completionMap]
  exact (quotientMaximalIdealPowEquivAll R n).symm_apply_apply _

/-- The other inverse law is also verified on every native quotient coordinate. -/
theorem completionMap_completionMapInv
    (x : AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)) :
    completionMap R (completionMapInv R x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_completionMap, eval_completionMapInv]
  exact (quotientMaximalIdealPowEquivAll R n).apply_symm_apply _

/-- The actual completions are equivalent through the original infinitesimal maps. -/
def completionEquiv :
    AdicCompletion (maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (maximalIdeal (Henselization R)) (Henselization R) :=
  AlgEquiv.ofAlgHom (completionMap R) (completionMapInv R)
    (AlgHom.ext (completionMap_completionMapInv R))
    (AlgHom.ext (completionMapInv_completionMap R))

end Henselization
