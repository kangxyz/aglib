/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsIntegralBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.NormalBase
public import Aglib.RingTheory.Smooth.SplitSectionCompletion
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Original smooth completion over an arbitrary Hartogs open

The original ambient open only needs to contain its height-one points.
It is not replaced by the inverse image of a punctured coefficient spectrum.
Neither the completion nor the base-changed finite algebra is assumed normal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (ε : B →ₐ[A] A) (U : (Spec (.of B)).Opens)

/-- The native completion projection retains the inverse image of the
specified original ambient open under the original section. -/
theorem smoothCompletionOpen_zeroSection :
    splitSectionOpen
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom
      (Spec.algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ U) =
        splitSectionOpen ε.toRingHom U := by
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let π : P →ₐ[A] A :=
    AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)
  have hπ : CommRingCat.ofHom (algebraMap B P) ≫ CommRingCat.ofHom π.toRingHom =
      CommRingCat.ofHom ε.toRingHom := by
    ext b
    exact AdicCompletion.kerProj_of (Algebra.Smooth.splitSection_surjective ε) b
  have h : Spec.map (CommRingCat.ofHom π.toRingHom) ≫ Spec.algebraMap B P =
      Spec.map (CommRingCat.ofHom ε.toRingHom) := by
    rw [← Spec.map_comp, hπ]
  change Spec.map (CommRingCat.ofHom π.toRingHom) ⁻¹ᵁ
    (Spec.algebraMap B P ⁻¹ᵁ U) = _
  rw [← Hom.comp_preimage, h]

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra.Smooth A B] [Nonempty U]

/-- Original scalar sections of the completion over any ambient Hartogs
open are bijective; no zero-section or punctured-open equality is needed. -/
theorem smoothCompletionOpenScalar_bijective
    (hU : ∀ p : PrimeSpectrum B, p.asIdeal.height = 1 → p ∈ U) :
    Function.Bijective (affineScalarMap
      (Spec.algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ U).ι) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : IsIntegrallyClosed B := Algebra.Smooth.isIntegrallyClosed_of_normalBase A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  have hscalar : Function.Bijective (affineScalarMap U.ι) := by
    have h := hartogsScalarMap_bijective B U hU
    rw [← affineScalarMap_topIso U] at h
    exact Function.Bijective.of_comp_left
      (f := U.topIso.hom.hom) (g := affineScalarMap U.ι) h
      (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
  exact Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (Spec.algebraMap B P ∣_ U) (algebraMap B P) (Spec.algebraMap B P ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict (Spec.algebraMap B P) U)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hscalar

/-- The original finite normal algebra, after actual completion base change,
has unchanged scalar sections over the same arbitrary ambient Hartogs open. -/
theorem smoothCompletionFiniteOpenScalar_bijective
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra B C] [FaithfulSMul B C] [Module.Finite B C]
    (hU : ∀ p : PrimeSpectrum B, p.asIdeal.height = 1 → p ∈ U) :
    Function.Bijective (affineScalarMap
      (Spec.algebraMap (AdicCompletion (RingHom.ker ε.toRingHom) B)
        ((AdicCompletion (RingHom.ker ε.toRingHom) B) ⊗[B] C) ⁻¹ᵁ
        (Spec.algebraMap B (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ U)).ι) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  let : IsIntegrallyClosed B := Algebra.Smooth.isIntegrallyClosed_of_normalBase A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let e : C ⊗[B] P ≃ₐ[C] D :=
    { __ := Algebra.TensorProduct.comm B C P, commutes' _ := rfl }
  let : Module.Flat C D := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let V := Spec.algebraMap B C ⁻¹ᵁ U
  have h := hartogsIntegralPullbackAffineScalar_bijective_of_flat B C U hU
    (algebraMap C D) (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (Spec.algebraMap C D ∣_ V) (Spec.algebraMap C D ⁻¹ᵁ V).ι
    (isPullback_morphismRestrict (Spec.algebraMap C D) V)
  have hm : Spec.algebraMap C D ≫ Spec.algebraMap B C =
      Spec.algebraMap P D ≫ Spec.algebraMap B P := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext b
    exact (IsScalarTower.algebraMap_apply B C D b).symm.trans
      (IsScalarTower.algebraMap_apply B P D b)
  have hVeq : Spec.algebraMap C D ⁻¹ᵁ V =
      Spec.algebraMap P D ⁻¹ᵁ (Spec.algebraMap B P ⁻¹ᵁ U) := by
    change Spec.algebraMap C D ⁻¹ᵁ (Spec.algebraMap B C ⁻¹ᵁ U) = _
    rw [← Hom.comp_preimage, hm, Hom.comp_preimage]
  exact hVeq ▸ h

end AlgebraicGeometry.Scheme
