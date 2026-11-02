/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.SplitSectionCompletion
public import Aglib.RingTheory.MvPowerSeries.AugmentationUniqueness

/-! # The whole original augmentation square of smooth section completion

The finite-variable polynomial coordinate equations force the full augmentation
square by algebraic uniqueness. This compares the canonical completion projection,
not a selected replacement map, and imposes no continuity premise.
-/

@[expose] public noncomputable section

namespace Algebra.Smooth

variable {R B σ : Type*} [CommRing R] [CommRing B] [Algebra R B] [Finite σ]
  (ε : B →ₐ[R] R)

/-- The polynomial equations force the full original augmentation on every series. -/
theorem splitSectionCompletion_augmentation
    (x : σ → RingHom.ker ε.toRingHom)
    (e : MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B)
    (he : ∀ p : MvPolynomial σ R, e (algebraMap _ (MvPowerSeries σ R) p) =
      algebraMap B _ (MvPolynomial.aeval (fun i => (x i).val) p)) :
    (AdicCompletion.kerProj (splitSection_surjective ε)).toRingHom.comp e.toRingHom =
      MvPowerSeries.constantCoeff := by
  apply MvPowerSeries.eq_constantCoeff_of_X
    ((AdicCompletion.kerProj (splitSection_surjective ε)).comp e.toAlgHom)
  intro i
  change AdicCompletion.kerProj (splitSection_surjective ε) (e (MvPowerSeries.X i)) = 0
  have h : e (MvPowerSeries.X i) =
      algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) (x i).val := by
    simpa only [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_X,
      MvPowerSeries.map_X, MvPolynomial.aeval_X] using he (MvPolynomial.X i)
  rw [h]
  change AdicCompletion.kerProj (splitSection_surjective ε)
    (AdicCompletion.of (RingHom.ker ε.toRingHom) B (x i).val) = 0
  exact (AdicCompletion.kerProj_of (splitSection_surjective ε) (x i).val).trans
    (x i).property

/-- Smooth split-section completion in small finite coordinates, retaining the full
original augmentation square as well as every polynomial-coordinate equation. -/
theorem exists_fin_splitSectionCompletion_augmentation
    {R : Type*} {B : Type*} [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B] (ε : B →ₐ[R] R) :
    ∃ (n : ℕ) (x : Fin n → RingHom.ker ε.toRingHom)
      (e : MvPowerSeries (Fin n) R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B),
      (∀ p : MvPolynomial (Fin n) R, e (algebraMap _ (MvPowerSeries (Fin n) R) p) =
        algebraMap B _ (MvPolynomial.aeval (fun i => (x i).val) p)) ∧
      (AdicCompletion.kerProj (splitSection_surjective ε)).toRingHom.comp e.toRingHom =
        MvPowerSeries.constantCoeff := by
  obtain ⟨n, x, e, he⟩ := exists_fin_splitSectionCompletionAlgEquiv ε
  exact ⟨n, x, e, he, splitSectionCompletion_augmentation ε x e he⟩

end Algebra.Smooth
