/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionPrescribedSection
public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionSection
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.AffinePointwiseFlatBaseChange

/-! # Purity along the original smooth section

A finite normal cover of a smooth domain over a normal local base, etale over
the punctured base, is etale along its prescribed lifted section. Completion
is used only internally; the conclusion concerns the original finite map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- Punctured etaleness extends along the original lifted smooth section.
No normality of the completion or tensor product is required. -/
theorem smoothSection_etaleAt_of_punctured
    (A B C : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra B C] [FaithfulSMul B C] [Module.Finite B C]
    (ε : B →ₐ[A] A) (δ : C →+* A)
    (hδ : δ.comp (algebraMap B C) = ε.toRingHom)
    (hdim : 2 ≤ ringKrullDim A)
    [Etale (Spec.algebraMap B C ∣_
      (Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A))] :
    ∀ x : Spec (.of A),
      (Spec.algebraMap B C).etaleAt ((Spec.map (CommRingCat.ofHom δ)) x) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : Algebra.FinitePresentation B C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let U := Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A
  let W := Spec.algebraMap A P ⁻¹ᵁ puncturedSpecOpen A
  have hbase : Spec.algebraMap B P ≫ Spec.algebraMap A B =
      Spec.algebraMap A P := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
  have hW : Spec.algebraMap B P ⁻¹ᵁ U = W := by
    change Spec.algebraMap B P ⁻¹ᵁ (Spec.algebraMap A B ⁻¹ᵁ _) = _
    rw [← Hom.comp_preimage, hbase]
  have het := Hom.property_morphismRestrict_of_isPullback (@Etale)
    (isPullback_tensorSpec B P C) U inferInstance
  let : Etale (Spec.algebraMap P D ∣_ W) := hW ▸ het
  obtain ⟨a, ha, hright⟩ := smoothCompletion_exists_section ε δ hδ
  have hpoint := smoothCompletion_etaleAt_prescribedSection A B ε C hdim a ha
  intro x
  have hdesc := Hom.specAlgebraMap_etaleAt_of_flat_baseChange B C P (a x) (hpoint x)
  have he := congrArg (fun g : Spec (.of A) ⟶ Spec (.of C) => g x) hright
  exact he ▸ hdesc

end AlgebraicGeometry.Scheme
