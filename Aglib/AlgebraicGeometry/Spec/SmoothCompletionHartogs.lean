/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsSmoothFiniteBaseChange
public import Aglib.RingTheory.Smooth.SplitSectionCompletion
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Original Hartogs scalars on smooth section completion

The ambient completion and its finite normal algebra base change are the
literal adic completion and tensor product. Flat base change supplies their
punctured scalar identifications without assuming either new ring normal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (ε : B →ₐ[A] A)

/-- The original completion augmentation has precisely the punctured base
as inverse image of the original punctured completion open. -/
theorem smoothCompletionPuncturedOpen_zeroSection [IsLocalRing A] :
    splitSectionOpen
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom
      (Spec.algebraMap A (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ
        puncturedSpecOpen A) = puncturedSpecOpen A := by
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let π : P →ₐ[A] A :=
    AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)
  have h : Spec.map (CommRingCat.ofHom π.toRingHom) ≫ Spec.algebraMap A P =
      𝟙 (Spec (.of A)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact π.commutes a
  change Spec.map (CommRingCat.ofHom π.toRingHom) ⁻¹ᵁ
    (Spec.algebraMap A P ⁻¹ᵁ puncturedSpecOpen A) = _
  rw [← Hom.comp_preimage, h]
  rfl

variable [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [IsDomain B] [Algebra.Smooth A B]

/-- The actual scalar map of the punctured completion open is bijective.
Normality of the completion is neither assumed nor used. -/
theorem smoothCompletionPuncturedScalar_bijective (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (affineScalarMap
      (Spec.algebraMap A (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ
        puncturedSpecOpen A).ι) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let U := Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A
  have hU : Function.Bijective (affineScalarMap U.ι) := by
    have h := hartogsSmoothPuncturedPullbackScalar_bijective A B hdim
    rw [← affineScalarMap_topIso U] at h
    exact Function.Bijective.of_comp_left
      (f := U.topIso.hom.hom) (g := affineScalarMap U.ι) h
      (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
  have h := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (Spec.algebraMap B P ∣_ U) (algebraMap B P) (Spec.algebraMap B P ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict (Spec.algebraMap B P) U)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hU
  have hm : Spec.algebraMap B P ≫ Spec.algebraMap A B = Spec.algebraMap A P := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  have hUeq : Spec.algebraMap B P ⁻¹ᵁ U = Spec.algebraMap A P ⁻¹ᵁ
      puncturedSpecOpen A := by
    change Spec.algebraMap B P ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ _) = _
    rw [← Hom.comp_preimage, hm]
  exact hUeq ▸ h

/-- The actual tensor-base-changed finite normal source retains its original
Hartogs scalar map over the punctured completion open. Neither completion
nor tensor product is assumed normal or a domain. -/
theorem smoothCompletionFinitePuncturedScalar_bijective
    (C : Type u) [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra B C] [FaithfulSMul B C] [Module.Finite B C]
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (affineScalarMap
      (Spec.algebraMap (AdicCompletion (RingHom.ker ε.toRingHom) B)
        ((AdicCompletion (RingHom.ker ε.toRingHom) B) ⊗[B] C) ⁻¹ᵁ
        (Spec.algebraMap A (AdicCompletion (RingHom.ker ε.toRingHom) B) ⁻¹ᵁ
          puncturedSpecOpen A)).ι) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let e : C ⊗[B] P ≃ₐ[C] D :=
    { __ := Algebra.TensorProduct.comm B C P, commutes' _ := rfl }
  let : Module.Flat C D := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let U := Spec.algebraMap B C ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A)
  have h := hartogsSmoothFiniteScalar_bijective_of_flat A B C hdim
    (algebraMap C D) (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (Spec.algebraMap C D ∣_ U) (Spec.algebraMap C D ⁻¹ᵁ U).ι
    (isPullback_morphismRestrict (Spec.algebraMap C D) U)
  have hm : Spec.algebraMap C D ≫ Spec.algebraMap B C =
      Spec.algebraMap P D ≫ Spec.algebraMap B P := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext b
    exact (IsScalarTower.algebraMap_apply B C D b).symm.trans
      (IsScalarTower.algebraMap_apply B P D b)
  have hUeq : Spec.algebraMap C D ⁻¹ᵁ U = Spec.algebraMap P D ⁻¹ᵁ
      (Spec.algebraMap A P ⁻¹ᵁ puncturedSpecOpen A) := by
    change Spec.algebraMap C D ⁻¹ᵁ
      (Spec.algebraMap B C ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ _)) = _
    rw [← Hom.comp_preimage, hm, Hom.comp_preimage]
    congr 1
  exact hUeq ▸ h

end AlgebraicGeometry.Scheme
