/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual fraction-field base change along a local DVR map

Inverting the original uniformizer proves the pushout, rather than assuming a generic-fiber
isomorphism. The map may be ramified.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

open TensorProduct

variable (R A F B : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsFractionRing A B]
  [Algebra F B] [IsScalarTower R F B]

/-- The square of a local injective DVR map and its actual fraction maps is a pushout. -/
theorem fraction_isPushout (hinj : Function.Injective (algebraMap R A)) :
    Algebra.IsPushout R A F B := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have : IsLocalization.Away π F :=
    isLocalizationAway_of_nonzero_nonunit F hπ.ne_zero hπ.not_isUnit
  have hπA : algebraMap R A π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ.ne_zero
  have hπAu : ¬ IsUnit (algebraMap R A π) := fun h ↦ hπ.not_isUnit (IsUnit.of_map _ π h)
  have : IsLocalization.Away (algebraMap R A π) B :=
    isLocalizationAway_of_nonzero_nonunit B hπA hπAu
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers π)) B := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization.Away (algebraMap R A π) B)
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers π) F A B

/-- Actual generic scalar extension is obtained by canceling the proved fraction pushout. -/
def fractionBaseChangeAlgEquiv (hinj : Function.Injective (algebraMap R A))
    (E : Type*) [CommRing E] [Algebra R E] [Algebra F E] [IsScalarTower R F E] :
    B ⊗[F] E ≃ₐ[A] A ⊗[R] E := by
  letI := fraction_isPushout R A F B hinj
  exact Algebra.IsPushout.cancelBaseChangeAlg R A F B E

@[simp] theorem fractionBaseChangeAlgEquiv_symm_tmul
    (hinj : Function.Injective (algebraMap R A))
    (E : Type*) [CommRing E] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    (a : A) (x : E) :
    (fractionBaseChangeAlgEquiv R A F B hinj E).symm (a ⊗ₜ[R] x) =
      algebraMap A B a ⊗ₜ[F] x := by
  simp [fractionBaseChangeAlgEquiv]

end IsDiscreteValuationRing
