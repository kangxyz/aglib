/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionOpenPrescribedSection
public import Aglib.AlgebraicGeometry.Spec.SmoothCompletionSection
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.AffinePointwiseFlatBaseChange

/-! # Purity along a smooth section from its actual Hartogs open

The supplied original open contains every height-one point of the smooth
ambient domain and meets the section in its puncture. It need not be the
whole inverse image of the punctured base. The conclusion is on the original
finite map, not its completion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- The original finite normal cover is etale along its lifted section once
its actual Hartogs open is etale and meets that section in the puncture. -/
theorem smoothSection_etaleAt_of_hartogsOpen
    (A B C : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Smooth A B]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra B C] [FaithfulSMul B C] [Module.Finite B C]
    (ε : B →ₐ[A] A) (δ : C →+* A)
    (hδ : δ.comp (algebraMap B C) = ε.toRingHom)
    (U : (Spec (.of B)).Opens)
    (hheight : ∀ p : PrimeSpectrum B, p.asIdeal.height = 1 → p ∈ U)
    (hzero : Spec.map (CommRingCat.ofHom ε.toRingHom) ⁻¹ᵁ U = puncturedSpecOpen A)
    (hdim : 2 ≤ ringKrullDim A) [Etale (Spec.algebraMap B C ∣_ U)] :
    ∀ x : Spec (.of A),
      (Spec.algebraMap B C).etaleAt ((Spec.map (CommRingCat.ofHom δ)) x) := by
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : Algebra.FinitePresentation B C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := AdicCompletion (RingHom.ker ε.toRingHom) B
  let D := P ⊗[B] C
  let W := Spec.algebraMap B P ⁻¹ᵁ U
  let : Etale (Spec.algebraMap P D ∣_ W) :=
    Hom.property_morphismRestrict_of_isPullback (@Etale)
      (isPullback_tensorSpec B P C) U inferInstance
  obtain ⟨a, ha, hright⟩ := smoothCompletion_exists_section ε δ hδ
  have hpoint := smoothCompletion_etaleAt_prescribedSection_of_open
    A B ε C U hheight hzero hdim a ha
  intro x
  have hdesc := Hom.specAlgebraMap_etaleAt_of_flat_baseChange B C P (a x) (hpoint x)
  have he := congrArg (fun g : Spec (.of A) ⟶ Spec (.of C) => g x) hright
  exact he ▸ hdesc

end AlgebraicGeometry.Scheme
