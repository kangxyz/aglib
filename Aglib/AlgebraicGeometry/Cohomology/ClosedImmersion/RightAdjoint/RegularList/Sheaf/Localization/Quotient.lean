/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The original quotient-away ring equivalence

The quotient-kernel equivalence of the original surjective localization map
identifies `R_t / I R_t` with `(R / I)_[t]`. This focused public interface uses
the same native factories and literal map as the private implementation in
the closed-adjoint localization provider.
-/

@[expose] public noncomputable section

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (t : R)

/-- The original quotient-localization ring equivalence induced by the native Away map. -/
def quotientAwayRingEquiv :
    (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t))) ≃+*
      Localization.Away (Ideal.Quotient.mk I t) :=
  (Ideal.quotEquivOfEq (J := RingHom.ker
      (IsLocalization.Away.map (Localization.Away t)
        (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t))
      (by
        have h := CommRingCat.ker_localizationAway_map
          (CommRingCat.ofHom (Ideal.Quotient.mk I)) t
        change RingHom.ker (IsLocalization.Away.map (Localization.Away t)
            (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t) =
          (RingHom.ker (Ideal.Quotient.mk I)).map (algebraMap R (Localization.Away t)) at h
        simpa only [Ideal.mk_ker] using h.symm)).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := IsLocalization.Away.map (Localization.Away t)
        (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t)
      (IsLocalization.map_surjective_of_surjective (Submonoid.powers t)
        (Localization.Away t) (Localization.Away (Ideal.Quotient.mk I t))
        Ideal.Quotient.mk_surjective))

/-- A quotient representative maps by the literal original localization homomorphism. -/
theorem quotientAwayRingEquiv_mk (a : Localization.Away t) :
    quotientAwayRingEquiv I t
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t))) a) =
        IsLocalization.Away.map (Localization.Away t)
          (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t a := by
  simp only [quotientAwayRingEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := IsLocalization.Away.map (Localization.Away t)
      (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t)
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers t)
      (Localization.Away t) (Localization.Away (Ideal.Quotient.mk I t))
      Ideal.Quotient.mk_surjective) a
