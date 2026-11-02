/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients

/-! # Original coefficient squares commute with cone triangles -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma triangleCoefficientMap_square {X₀ X₁ Y₀ Y₁ Z W : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (l : W ⟶ Z) (p₀ : Z ⟶ X₀) (p₁ : Z ⟶ X₁) (q₀ : W ⟶ Y₀) (q₁ : W ⟶ Y₁)
    (he : v₁ ≫ f = h ≫ v₀) (hp : p₁ ≫ f = p₀) (hq : q₁ ≫ h = q₀)
    (hi : q₀ ≫ v₀ = l ≫ p₀) (hj : q₁ ≫ v₁ = l ≫ p₁)
    {F : AbelianSheaf.{u, u + 1} X₀} {G : AbelianSheaf.{u, u + 1} X₁}
    (φ : (inverseImage f).obj F ⟶ G) :
    triangleCoefficientMap h q₀ q₁ hq (squareCoefficientMap v₀ v₁ f h he φ) ≫
        (inverseImageSquareIso p₁ q₁ v₁ l hj).hom.app G =
      (inverseImageSquareIso p₀ q₀ v₀ l hi).hom.app F ≫
        (inverseImage l).map (triangleCoefficientMap f p₀ p₁ hp φ) := by
  subst p₀
  subst q₀
  have hs := inverseImageSquareIso_vComp f p₁ h q₁ v₀ v₁ l he.symm hj hi F
  rw [inverseImageSquareIso_transpose v₀ v₁ f h he, Iso.symm_hom] at hs
  have hn := (inverseImageSquareIso p₁ q₁ v₁ l hj).hom.naturality φ
  have ht := congrArg
    (fun z => z ≫ (inverseImage l).map ((inverseImage p₁).map φ)) hs
  dsimp only [triangleCoefficientMap, squareCoefficientMap, pullbackTriangleIso,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
