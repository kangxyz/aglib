/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.MappedAffineCoverModels
/-! # Actual mapped affine covering data at one stage -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v

/-- An actual covering model with both refinement triangles. Its construction is
independent of the coefficient sheaf and its sections. -/
structure MappedCoverModel {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    {J : Type v} (Y : J → Over c.pt) (U : J → X.Etale)
    (a : ∀ j, (Y j).left ⟶ (U j).left) where
  /-- The common stage carrying the descended covering charts. -/
  stage : I
  /-- The original transition from the chosen stage to the specified stage. -/
  toStage : stage ⟶ i
  /-- The actual family of affine etale charts over the chosen stage. -/
  cover : J → Over (D.obj stage)
  affine : ∀ j, IsAffine (cover j).left
  etale : ∀ j, Etale (cover j).hom
  covers : ∀ x : D.obj stage, ∃ j, ∃ y : (cover j).left, (cover j).hom y = x
  /-- The descended map from each chart to its original etale test object. -/
  representative : ∀ j, (cover j).left ⟶ (U j).left
  /-- The original refinement map after pulling each chart back to the limit. -/
  refinement : ∀ j, pullback (c.π.app stage) (cover j).hom ⟶ (Y j).left
  representative_w : ∀ j, representative j ≫ (U j).hom =
    (cover j).hom ≫ (D.map toStage ≫ r)
  refinement_w : ∀ j, refinement j ≫ (Y j).hom =
    pullback.fst (c.π.app stage) (cover j).hom
  refinement_representative : ∀ j, refinement j ≫ a j =
    pullback.snd (c.π.app stage) (cover j).hom ≫ representative j

/-- Construct the covering model by actual finite-presentation descent. -/
def mappedCoverModel {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    {J : Type v} [Finite J] (Y : J → Over c.pt)
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (Y j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (Y j).hom ≫ (c.π.app i ≫ r)) :
    MappedCoverModel D c i r Y U a := Classical.choice (by
  obtain ⟨k, q, W, hW, he, hcov, b, d, hb, hd, hda⟩ :=
    exists_mapped_affine_cover_model D c hc i r Y hcover U a ha
  exact ⟨⟨k, q, W, hW, he, hcov, b, d, hb, hd, hda⟩⟩)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
