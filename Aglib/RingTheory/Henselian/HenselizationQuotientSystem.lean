/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationQuotient

/-!
# The full infinitesimal quotient system of henselization

The zero-power quotient is treated as a zero ring, not as a local ring.
All quotient equivalences use the original induced maps and respect the native
power transition maps, providing the inverse systems needed for completion.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Bijectivity on all powers, including the zero-ring quotient at power zero. -/
theorem quotientMaximalIdealPowMap_bijective_all (n : ℕ) :
    Function.Bijective (quotientMaximalIdealPowMap R n) := by
  by_cases hn : n = 0
  · subst n
    let : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    let : Subsingleton (Henselization R ⧸ maximalIdeal (Henselization R) ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  · exact quotientMaximalIdealPowMap_bijective R n hn

/-- The original quotient-map equivalence for every nonnegative power. -/
def quotientMaximalIdealPowEquivAll (n : ℕ) :
    (R ⧸ (maximalIdeal R ^ n)) ≃ₐ[R]
      (Henselization R ⧸ (maximalIdeal (Henselization R) ^ n)) :=
  AlgEquiv.ofBijective (quotientMaximalIdealPowMap R n)
    (quotientMaximalIdealPowMap_bijective_all R n)

/-- The original induced quotient maps commute with the native power transitions. -/
theorem quotientMaximalIdealPowMap_factorPow {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal (Henselization R)) hmn).comp
        (quotientMaximalIdealPowMap R n).toRingHom =
      (quotientMaximalIdealPowMap R m).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal R) hmn) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The inverse quotient equivalences also commute with the native transitions. -/
theorem quotientMaximalIdealPowEquivAll_symm_factorPow {m n : ℕ} (hmn : m ≤ n)
    (x : Henselization R ⧸ maximalIdeal (Henselization R) ^ n) :
    (quotientMaximalIdealPowEquivAll R m).symm
        (Ideal.Quotient.factorPow (maximalIdeal (Henselization R)) hmn x) =
      Ideal.Quotient.factorPow (maximalIdeal R) hmn
        ((quotientMaximalIdealPowEquivAll R n).symm x) := by
  apply (quotientMaximalIdealPowEquivAll R m).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := RingHom.congr_fun (quotientMaximalIdealPowMap_factorPow R hmn)
    ((quotientMaximalIdealPowEquivAll R n).symm x)
  change Ideal.Quotient.factorPow (maximalIdeal (Henselization R)) hmn
      ((quotientMaximalIdealPowEquivAll R n)
        ((quotientMaximalIdealPowEquivAll R n).symm x)) =
    (quotientMaximalIdealPowEquivAll R m)
      (Ideal.Quotient.factorPow (maximalIdeal R) hmn
        ((quotientMaximalIdealPowEquivAll R n).symm x)) at h
  simpa only [AlgEquiv.apply_symm_apply] using h

end Henselization
