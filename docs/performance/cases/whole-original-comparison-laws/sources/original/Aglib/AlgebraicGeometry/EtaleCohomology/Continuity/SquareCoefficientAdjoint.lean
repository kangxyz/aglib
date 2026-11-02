/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # Original square coefficient maps under the two composite adjunctions -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma directImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    directImageSquareIso g g' f f' e.symm = (directImageSquareIso f f' g g' e).symm := by
  simp only [directImageSquareIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

lemma conjugate_inverseImageSquareIso_inv {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    conjugateEquiv ((inverseImageAdjunction g).comp (inverseImageAdjunction f'))
        ((inverseImageAdjunction f).comp (inverseImageAdjunction g'))
        (inverseImageSquareIso f f' g g' e).inv =
      (directImageSquareIso f f' g g' e).inv := by
  have ht := conjugateEquiv_inverseImageSquareIso_hom g g' f f' e.symm
  rw [inverseImageSquareIso_transpose f f' g g' e,
    directImageSquareIso_transpose f f' g g' e] at ht
  exact ht

lemma squareCoefficientMap_homEquiv {X₀ X₁ Y₀ Y₁ : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (he : v₁ ≫ f = h ≫ v₀)
    {F : AbelianSheaf.{u, u + 1} X₀} {G : AbelianSheaf.{u, u + 1} X₁}
    {K : AbelianSheaf.{u, u + 1} Y₁}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage v₁).obj G ⟶ K) :
    ((inverseImageAdjunction v₀).comp (inverseImageAdjunction h)).homEquiv _ _
        (squareCoefficientMap v₀ v₁ f h he φ ≫ ψ) =
      (inverseImageAdjunction f).homEquiv _ _ φ ≫
        (directImage f).map ((inverseImageAdjunction v₁).homEquiv _ _ ψ) ≫
          (directImageSquareIso v₀ v₁ f h he).inv.app K := by
  have ht := homEquiv_precomp_conjugate
    ((inverseImageAdjunction f).comp (inverseImageAdjunction v₁))
    ((inverseImageAdjunction v₀).comp (inverseImageAdjunction h))
    (inverseImageSquareIso v₀ v₁ f h he).inv ((inverseImage v₁).map φ ≫ ψ)
  rw [conjugate_inverseImageSquareIso_inv] at ht
  have hc : ((inverseImageAdjunction f).comp (inverseImageAdjunction v₁)).homEquiv _ _
      ((inverseImage v₁).map φ ≫ ψ) =
        (inverseImageAdjunction f).homEquiv _ _ φ ≫
          (directImage f).map ((inverseImageAdjunction v₁).homEquiv _ _ ψ) := by
    rw [Adjunction.comp_homEquiv]
    change (inverseImageAdjunction f).homEquiv _ _
      ((inverseImageAdjunction v₁).homEquiv _ _ ((inverseImage v₁).map φ ≫ ψ)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hn := congrArg
    (fun z : F ⟶ (directImage f).obj ((directImage v₁).obj K) =>
      z ≫ (directImageSquareIso v₀ v₁ f h he).inv.app K) hc
  simpa only [squareCoefficientMap, Category.assoc] using ht.trans hn

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
