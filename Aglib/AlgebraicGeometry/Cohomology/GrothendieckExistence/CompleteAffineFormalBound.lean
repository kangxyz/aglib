/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompleteAffineModificationBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompleteEffectivity
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.IndependentFormalQuotientDefects

/-! # Uniform exceptional bounds for every complete affine formal source

Native affine effectivity supplies the source algebraization. Naturality of
the original formal-functions comparison retains the specified upstairs
isomorphism, so the bound applies to the original formal source itself.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  (J : Ideal B) [IsAdicComplete J B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p]
  (F : AdicSystem (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J))
  (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).obj F ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J)).obj G)

/-- Over a complete affine base the specified modification comparison has
one positive exceptional exponent, independent of the formal stage. -/
theorem affineModificationComparison_hasBoundedDefects_of_complete
    (K : (Spec B).IdealSheafData) (U : (Spec B).Opens) [IsIso (p ∣_ U)]
    (hU : (U : Set (Spec B))ᶜ ⊆ K.support) :
    AdicSystem.HasBoundedDefects K (affineModificationComparison p J F G β.hom) := by
  obtain ⟨M, ⟨e⟩⟩ := Cohomology.affineComplete_completion_essImage B J F
  let β' := (baseIdealPullbackFunctor p (𝟙 (Spec B)) J).mapIso e ≪≫ β
  obtain ⟨t, ht, h⟩ :=
    affineModificationComparison_complete_hasBoundedDefects J p M G β' K U hU
  refine ⟨t, ht, h.of_iso_square e.symm (Iso.refl _) ?_⟩
  simp only [Iso.refl_hom, Category.comp_id]
  have he := affineModificationComparison_naturality p J F G β.hom _ e.hom
  change e.hom ≫ affineModificationComparison p J F G β.hom =
    affineModificationComparison p J
      ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj M)
      G β'.hom at he
  rw [← he]
  exact (Iso.inv_hom_id_assoc e _).symm

end AlgebraicGeometry.Scheme.Modules.Coherent
