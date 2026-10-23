/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution

/-! # Cover augmentation at an independent coefficient universe

This extends the original augmentation result without changing its complexes or
maps. The sheafification hypotheses are explicit at the supplied value universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Presheaf.Cech

universe c h w

variable {C : Type c} [Category.{h} C]
  {F G : Cᵒᵖ ⥤ Type w} (coverMap : F ⟶ G)
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective (Type w)]
  [J.PreservesSheafification AddCommGrpCat.free.{w}]
  [IsLocallySurjective J coverMap]

/-- Local surjectivity makes the pointwise image and the target have the same free sheaf. -/
theorem freeImageInclusion_sheafify_isIso_of_sizes :
    IsIso ((presheafToSheaf J AddCommGrpCat).map
      (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)) := by
  have hi : IsLocallyInjective J (Subfunctor.range coverMap).ι := by
    apply isLocallyInjective_of_injective
    intro U
    exact Subtype.val_injective
  have hs : IsLocallySurjective J (Subfunctor.range coverMap).ι :=
    isLocallySurjective_of_isLocallySurjective_fac J (Subfunctor.toRange_ι coverMap)
  rw [← J.W_iff]
  apply J.W_of_preservesSheafification AddCommGrpCat.free
  exact J.W_of_isLocallyBijective (Subfunctor.range coverMap).ι

/-- A locally surjective set-presheaf map has the genuine sheafified free Čech resolution. -/
theorem sheafAugmentation_quasiIso_of_sizes : QuasiIso (sheafAugmentation coverMap J) := by
  have := freeImageAugmentation_quasiIso coverMap
  have := freeImageInclusion_sheafify_isIso_of_sizes coverMap J
  let S := presheafToSheaf J AddCommGrpCat.{w}
  have hq : QuasiIso ((S.mapHomologicalComplex _).map (freeImageAugmentation coverMap)) :=
    inferInstance
  have hm : IsIso ((S.mapHomologicalComplex _).map
      ((ChainComplex.single₀ _).map
        (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free))) := by
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso
        (HomologicalComplex.singleMapHomologicalComplex S (.down ℕ) 0)
        (Arrow.mk (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)))).2
      (by
        change IsIso ((ChainComplex.single₀ _).map
          (S.map (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)))
        infer_instance)
  have hmid : QuasiIso ((S.mapHomologicalComplex _).map
      ((ChainComplex.single₀ _).map
        (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free))) := by
    infer_instance
  unfold sheafAugmentation
  rw [freeAugmentation_factor, Functor.map_comp]
  exact quasiIso_comp _ _ (hφ := quasiIso_comp _ _ (hφ := hq) (hφ' := hmid))


end CategoryTheory.Presheaf.Cech
