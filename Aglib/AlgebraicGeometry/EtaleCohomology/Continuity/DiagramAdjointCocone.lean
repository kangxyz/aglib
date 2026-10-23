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

/-- The native direct-image triangle, with its original equality transport. -/
def directImageTriangleIso {X Y T : Scheme.{u}} (f : Y ⟶ X)
    (p : T ⟶ X) (q : T ⟶ Y) (h : q ≫ f = p) :
    directImage q ⋙ directImage f ≅ directImage p :=
  directImageCompIso f q ≪≫ eqToIso (congrArg directImage h)

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
  subst p
  have ht := homEquiv_precomp_conjugate
    ((inverseImageAdjunction f).comp (inverseImageAdjunction q))
    (inverseImageAdjunction (q ≫ f)) (inverseImageComp f q).hom
    ((inverseImage q).map φ ≫ ψ)
  rw [conjugateEquiv_inverseImageComp_hom] at ht
  have hc : ((inverseImageAdjunction f).comp (inverseImageAdjunction q)).homEquiv _ _
      ((inverseImage q).map φ ≫ ψ) =
        (inverseImageAdjunction f).homEquiv _ _ φ ≫
          (directImage f).map ((inverseImageAdjunction q).homEquiv _ _ ψ) := by
    rw [Adjunction.comp_homEquiv]
    change (inverseImageAdjunction f).homEquiv _ _
      ((inverseImageAdjunction q).homEquiv _ _ ((inverseImage q).map φ ≫ ψ)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have he := ht.trans (congrArg (fun k => k ≫ (directImageCompIso f q).hom.app K) hc)
  simpa only [triangleCoefficientMap, pullbackTriangleIso, directImageTriangleIso,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id, Category.assoc] using he

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
  (F : DiagramCoefficientSystem X) [HasColimit (coneCoefficientFunctor X c F)]

/-- The original triangle for a transition and two specified cone projections. -/
def diagramDirectImageTriangle {i j : I} (a : i ⟶ j) :
    directImage (c.ι.app j).unop ⋙ directImage (X.map a).unop ≅
      directImage (c.ι.app i).unop :=
  directImageTriangleIso (X.map a).unop (c.ι.app i).unop (c.ι.app j).unop (coneSquare X c a)

/-- Transpose the actual coefficient-colimit injection through the original adjunction. -/
def diagramAdjointLeg (i : I) : F.obj i ⟶
    (directImage (c.ι.app i).unop).obj (colimit (coneCoefficientFunctor X c F)) :=
  (inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _
    (colimit.ι (coneCoefficientFunctor X c F) i)

/-- The actual adjoint legs satisfy the original right-transition cocone equation. -/
lemma diagramAdjointLeg_naturality {i j : I} (a : i ⟶ j) :
    diagramAdjointLeg X c F i = F.map a ≫
      (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫
        (diagramDirectImageTriangle X c a).hom.app (colimit (coneCoefficientFunctor X c F)) := by
  have ht := triangleCoefficientMap_homEquiv (X.map a).unop
    (c.ι.app i).unop (c.ι.app j).unop (coneSquare X c a)
    (diagramInverseTransition X F a) (colimit.ι (coneCoefficientFunctor X c F) j)
  have hw := congrArg ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _)
    (colimit.w (coneCoefficientFunctor X c F) a)
  have hm : (inverseImageAdjunction (X.map a).unop).homEquiv _ _
      (diagramInverseTransition X F a) = F.map a := Equiv.apply_symm_apply _ _
  exact hw.symm.trans (ht.trans (congrArg
    (fun k => k ≫ (directImage (X.map a).unop).map (diagramAdjointLeg X c F j) ≫
      (diagramDirectImageTriangle X c a).hom.app (colimit (coneCoefficientFunctor X c F))) hm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
