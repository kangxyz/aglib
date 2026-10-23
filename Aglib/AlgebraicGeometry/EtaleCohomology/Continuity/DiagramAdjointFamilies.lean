/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramAdjointCocone

/-! # Actual cocone families written through the original right adjoints -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- Original coefficient cocone naturality, before choosing a colimit target. -/
lemma diagramCoefficientMap_homEquiv {i j : I} (a : i ⟶ j)
    {K : AbelianSheaf.{u, u + 1} c.pt.unop}
    (ψ : (inverseImage (c.ι.app j).unop).obj (F.obj j) ⟶ K) :
    (inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _
        ((coneCoefficientFunctor X c F).map a ≫ ψ) =
      F.map a ≫ (directImage (X.map a).unop).map
        ((inverseImageAdjunction (c.ι.app j).unop).homEquiv _ _ ψ) ≫
          (diagramDirectImageTriangle X c a).hom.app K := by
  have ht := triangleCoefficientMap_homEquiv (X.map a).unop
    (c.ι.app i).unop (c.ι.app j).unop (coneSquare X c a)
    (diagramInverseTransition X F a) ψ
  have hm : (inverseImageAdjunction (X.map a).unop).homEquiv _ _
      (diagramInverseTransition X F a) = F.map a := Equiv.apply_symm_apply _ _
  exact ht.trans (congrArg
    (fun z : F.obj i ⟶ (directImage (X.map a).unop).obj (F.obj j) =>
      z ≫ (directImage (X.map a).unop).map
        ((inverseImageAdjunction (c.ι.app j).unop).homEquiv _ _ ψ) ≫
          (diagramDirectImageTriangle X c a).hom.app K) hm)

/-- Families of original right-adjoint legs with their actual compatibility equations. -/
def DiagramAdjointFamily (K : AbelianSheaf.{u, u + 1} c.pt.unop) :=
  {ξ : ∀ i, F.obj i ⟶ (directImage (c.ι.app i).unop).obj K //
    ∀ {i j} (a : i ⟶ j), ξ i = F.map a ≫
      (directImage (X.map a).unop).map (ξ j) ≫
        (diagramDirectImageTriangle X c a).hom.app K}

/-- This is a re-expression of actual cocones, not an assumed colimit comparison. -/
def diagramCoconeAdjointEquiv (K : AbelianSheaf.{u, u + 1} c.pt.unop) :
    (coneCoefficientFunctor X c F ⟶ (Functor.const I).obj K) ≃
      DiagramAdjointFamily X c F K where
  toFun α := ⟨fun i => (inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _ (α.app i),
    fun {i j} a => by
      have hn : (coneCoefficientFunctor X c F).map a ≫ α.app j = α.app i :=
        (α.naturality a).trans (Category.comp_id (α.app i))
      exact (congrArg ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _) hn).symm.trans
        (diagramCoefficientMap_homEquiv X c F a (α.app j))⟩
  invFun ξ :=
    { app := fun i => ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _).symm (ξ.val i)
      naturality := fun {i j} a => by
        change (coneCoefficientFunctor X c F).map a ≫
          ((inverseImageAdjunction (c.ι.app j).unop).homEquiv (F.obj j) K).symm
            (ξ.val j) =
          ((inverseImageAdjunction (c.ι.app i).unop).homEquiv (F.obj i) K).symm
            (ξ.val i) ≫ 𝟙 K
        rw [Category.comp_id]
        apply ((inverseImageAdjunction (c.ι.app i).unop).homEquiv (F.obj i) K).injective
        have ht := diagramCoefficientMap_homEquiv X c F a
          (((inverseImageAdjunction (c.ι.app j).unop).homEquiv (F.obj j) K).symm (ξ.val j))
        have he := congrArg
          (fun z : F.obj j ⟶ (directImage (c.ι.app j).unop).obj K =>
            F.map a ≫ (directImage (X.map a).unop).map z ≫
              (diagramDirectImageTriangle X c a).hom.app K)
          (((inverseImageAdjunction (c.ι.app j).unop).homEquiv (F.obj j) K).apply_symm_apply
            (ξ.val j))
        exact ht.trans (he.trans ((ξ.property a).symm.trans
          (((inverseImageAdjunction (c.ι.app i).unop).homEquiv (F.obj i) K).apply_symm_apply
            (ξ.val i)).symm)) }
  left_inv α := by
    apply NatTrans.ext
    funext i
    exact Equiv.symm_apply_apply _ _
  right_inv ξ := by
    apply Subtype.ext
    funext i
    exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
