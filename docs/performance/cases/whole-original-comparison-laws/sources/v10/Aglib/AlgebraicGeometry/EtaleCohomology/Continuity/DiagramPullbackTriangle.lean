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

private lemma schemeTriangleSquare_whole {X₀ X₁ Y₀ Y₁ Z W : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (l : W ⟶ Z) (p₀ : Z ⟶ X₀) (p₁ : Z ⟶ X₁) (q₀ : W ⟶ Y₀) (q₁ : W ⟶ Y₁)
    (he : v₁ ≫ f = h ≫ v₀) (hp : p₁ ≫ f = p₀) (hq : q₁ ≫ h = q₀)
    (hi : q₀ ≫ v₀ = l ≫ p₀) (hj : q₁ ≫ v₁ = l ≫ p₁) :
    Adjunction.CoefficientSquares.WholeTriangleSquareEquation
      (pullbackTriangleIso p₀ f p₁ hp) (pullbackTriangleIso q₀ h q₁ hq)
      (inverseImageSquareIso v₀ v₁ f h he)
      (inverseImageSquareIso p₀ q₀ v₀ l hi)
      (inverseImageSquareIso p₁ q₁ v₁ l hj) := by
  refine schemeAdjunctionData.triangleSquare_whole_of_eq schemeAdjunctionData_coherent
    f.op h.op v₀.op v₁.op l.op p₀.op p₁.op q₀.op q₁.op
    (congrArg Quiver.Hom.op he) (congrArg Quiver.Hom.op hp) (congrArg Quiver.Hom.op hq)
    (congrArg Quiver.Hom.op hi) (congrArg Quiver.Hom.op hj)
    (pullbackTriangleIso p₀ f p₁ hp) (pullbackTriangleIso q₀ h q₁ hq)
    (inverseImageSquareIso v₀ v₁ f h he)
    (inverseImageSquareIso p₀ q₀ v₀ l hi)
    (inverseImageSquareIso p₁ q₁ v₁ l hj) ?_ ?_ ?_ ?_ ?_
  · simpa only [Quiver.Hom.unop_op] using
      (schemeTriangleIso_eq_pullbackTriangleIso f.op p₀.op p₁.op
        (congrArg Quiver.Hom.op hp)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeTriangleIso_eq_pullbackTriangleIso h.op q₀.op q₁.op
        (congrArg Quiver.Hom.op hq)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeSquareIso_eq_inverseImageSquareIso v₀.op v₁.op f.op h.op
        (congrArg Quiver.Hom.op he)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeSquareIso_eq_inverseImageSquareIso p₀.op q₀.op v₀.op l.op
        (congrArg Quiver.Hom.op hi)).symm
  · simpa only [Quiver.Hom.unop_op] using
      (schemeSquareIso_eq_inverseImageSquareIso p₁.op q₁.op v₁.op l.op
        (congrArg Quiver.Hom.op hj)).symm

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
  exact Adjunction.CoefficientSquares.triangle_square
    (pullbackTriangleIso p₀ f p₁ hp) (pullbackTriangleIso q₀ h q₁ hq)
    (inverseImageSquareIso v₀ v₁ f h he)
    (inverseImageSquareIso p₀ q₀ v₀ l hi)
    (inverseImageSquareIso p₁ q₁ v₁ l hj)
    (schemeTriangleSquare_whole f h v₀ v₁ l p₀ p₁ q₀ q₁ he hp hq hi hj) φ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
