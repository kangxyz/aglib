/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIterationAmbient

/-! # Universal source isomorphisms for two given Cartesian presentations -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X X₁ X₂ S T U : Scheme.{u}}
  (f : X ⟶ S) (f₁ : X₁ ⟶ T) (f₂ : X₂ ⟶ U)
  (b : T ⟶ S) (c : U ⟶ T) (a : X₁ ⟶ X) (d : X₂ ⟶ X₁)
  (sq₁ : IsPullback a f₁ f b) (sq₂ : IsPullback d f₂ f₁ c)

/-- Actual pullback of the first presentation's universal source isomorphism. -/
def cartesianPresentationPullbackIso :
    pullback c f₁ ≅ pullback c (pullback.fst b f) :=
  asIso (pullback.map c f₁ c (pullback.fst b f)
    (𝟙 U) sq₁.flip.isoPullback.hom (𝟙 T)
    ((Category.comp_id c).trans (Category.id_comp c).symm)
    ((Category.comp_id f₁).trans sq₁.flip.isoPullback_hom_fst.symm))

@[reassoc]
theorem cartesianPresentationPullbackIso_hom_fst :
    (cartesianPresentationPullbackIso f f₁ b c a sq₁).hom ≫
        pullback.fst c (pullback.fst b f) = pullback.fst c f₁ := by
  simp only [cartesianPresentationPullbackIso, asIso_hom, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem cartesianPresentationPullbackIso_hom_snd :
    (cartesianPresentationPullbackIso f f₁ b c a sq₁).hom ≫
        pullback.snd c (pullback.fst b f) =
      pullback.snd c f₁ ≫ sq₁.flip.isoPullback.hom := by
  exact pullback.lift_snd _ _ _

/-- The actual universal source map of the pasted square is the actual sequence of
universal maps, pulled-back source isomorphism and native pullback associator. -/
theorem cartesianPresentation_isoPullback_pasting :
    (sq₂.paste_horiz sq₁).flip.isoPullback =
      sq₂.flip.isoPullback ≪≫ cartesianPresentationPullbackIso f f₁ b c a sq₁ ≪≫
        pullbackRightPullbackFstIso b f c := by
  apply Iso.ext
  apply pullback.hom_ext
  · simp only [IsPullback.isoPullback_hom_fst, Iso.trans_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst,
      cartesianPresentationPullbackIso_hom_fst, IsPullback.isoPullback_hom_fst]
  · simp only [IsPullback.isoPullback_hom_snd, Iso.trans_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_snd,
      cartesianPresentationPullbackIso_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
