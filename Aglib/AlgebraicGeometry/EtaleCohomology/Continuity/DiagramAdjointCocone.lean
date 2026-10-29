/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeSquares

/-! # The original adjoints of coefficient-colimit injections

The cocone equation is transposed through the original inverse/direct-image
adjunctions and the native composition comparison. No continuity is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- Transposing the original coefficient triangle gives its right-adjoint triangle. -/
lemma triangleCoefficientMap_homEquiv {X Y T : Scheme.{u}} (f : Y ⟶ X)
    (p : T ⟶ X) (q : T ⟶ Y) (h : q ≫ f = p)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {K : AbelianSheaf.{u, u + 1} T}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage q).obj G ⟶ K) :
    (inverseImageAdjunction p).homEquiv _ _ (triangleCoefficientMap f p q h φ ≫ ψ) =
      (inverseImageAdjunction f).homEquiv _ _ φ ≫
        (directImage f).map ((inverseImageAdjunction q).homEquiv _ _ ψ) ≫
          (directImageTriangleIso f p q h).hom.app K := by
  simpa only [triangleCoefficientMap, Category.assoc] using
    Adjunction.RepresentedCoherence.homEquiv_comp
      (inverseImageAdjunction f) (inverseImageAdjunction q) (inverseImageAdjunction p)
      (pullbackTriangleIso p f q h).hom (directImageTriangleIso f p q h).hom
      (pullbackTriangleIso_mate f p q h) F G K φ ψ

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
  (F : DiagramCoefficientSystem X) [hF : HasColimit (coneCoefficientFunctor X c F)]

/-- The original triangle for a transition and two specified cone projections. -/
def diagramDirectImageTriangle {i j : I} (a : i ⟶ j) :
    directImage (c.ι.app j).unop ⋙ directImage (X.map a).unop ≅
      directImage (c.ι.app i).unop :=
  directImageTriangleIso (X.map a).unop (c.ι.app i).unop (c.ι.app j).unop (coneSquare X c a)

/-- Transpose the actual coefficient-colimit injection through the original adjunction. -/
def diagramAdjointLeg (i : I) : F.obj i ⟶
    (directImage (c.ι.app i).unop).obj (colimit (coneCoefficientFunctor X c F)) := by
  letI : HasColimit ((diagramConeAdjunctionData X c).coefficientFunctor F) := hF
  exact (diagramConeAdjunctionData X c).adjointLeg F i

/-- The actual adjoint legs satisfy the original right-transition cocone equation. -/
lemma diagramAdjointLeg_naturality {i j : I} (a : i ⟶ j) :
    diagramAdjointLeg X c F i = F.map a ≫
      (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫
        (diagramDirectImageTriangle X c a).hom.app (colimit (coneCoefficientFunctor X c F)) := by
  let : HasColimit ((diagramConeAdjunctionData X c).coefficientFunctor F) := hF
  exact (diagramConeAdjunctionData X c).adjointLeg_naturality F a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
