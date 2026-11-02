/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SquareCoefficientAdjoint

/-! # The original pulled coefficient triangle under its two adjunctions -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma triangleSquareCoefficientMap_homEquiv {X₀ X₁ Y₀ Y₁ W : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (q₀ : W ⟶ Y₀) (q₁ : W ⟶ Y₁)
    (he : v₁ ≫ f = h ≫ v₀) (hq : q₁ ≫ h = q₀)
    {F : AbelianSheaf.{u, u + 1} X₀} {G : AbelianSheaf.{u, u + 1} X₁}
    {K : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G)
    (ψ : (inverseImage q₁).obj ((inverseImage v₁).obj G) ⟶ K) :
    (inverseImageAdjunction v₀).homEquiv _ _
        ((inverseImageAdjunction q₀).homEquiv _ _
          (triangleCoefficientMap h q₀ q₁ hq
            (squareCoefficientMap v₀ v₁ f h he φ) ≫ ψ)) =
      (inverseImageAdjunction f).homEquiv _ _ φ ≫
        (directImage f).map ((inverseImageAdjunction v₁).homEquiv _ _
          ((inverseImageAdjunction q₁).homEquiv _ _ ψ)) ≫
        (directImageSquareIso v₀ v₁ f h he).inv.app ((directImage q₁).obj K) ≫
        (directImage v₀).map ((directImageTriangleIso h q₀ q₁ hq).hom.app K) := by
  simpa only [Adjunction.CoefficientSquares.coefficientMap, triangleCoefficientMap,
    squareCoefficientMap, Category.assoc] using
    Adjunction.CoefficientSquares.triangle_homEquiv (inverseImageAdjunction f)
      (inverseImageAdjunction v₀) (inverseImageAdjunction v₁) (inverseImageAdjunction h)
      (inverseImageAdjunction q₀) (inverseImageAdjunction q₁)
      (inverseImageSquareIso v₀ v₁ f h he) (directImageSquareIso v₀ v₁ f h he)
      (conjugate_inverseImageSquareIso_inv v₀ v₁ f h he)
      (pullbackTriangleIso q₀ h q₁ hq) (directImageTriangleIso h q₀ q₁ hq)
      (pullbackTriangleIso_mate h q₀ q₁ hq) φ ψ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
