/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.FreeAbelianPullback
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of the native abelian inverse-image comparisons

The native direct images compose by precomposition. Adjunction uniqueness
therefore supplies the inverse-image comparison, with its original unit
normalization. The represented-section formulas identify its action on the
native free abelian sheaves on opens.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X Y Z : TopCat.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)

/-- The original abelian direct-image functors compose by native precomposition. -/
def abelianPushforwardCompIso :
    pushforward AddCommGrpCat.{u} q ⋙ pushforward AddCommGrpCat.{u} p ≅
      pushforward AddCommGrpCat.{u} (q ≫ p) := Iso.refl _

/-- The composite native inverse-image adjunction with its actual composite direct image. -/
def abelianPullbackCompAdjunction :
    pullback AddCommGrpCat.{u} p ⋙ pullback AddCommGrpCat.{u} q ⊣
      pushforward AddCommGrpCat.{u} (q ≫ p) :=
  ((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).comp
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} q)).ofNatIsoRight
      (abelianPushforwardCompIso p q)

/-- The canonical composite inverse-image comparison, normalized by the native adjunctions. -/
def abelianPullbackCompIso :
    pullback AddCommGrpCat.{u} p ⋙ pullback AddCommGrpCat.{u} q ≅
      pullback AddCommGrpCat.{u} (q ≫ p) :=
  (abelianPullbackCompAdjunction p q).leftAdjointUniq
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} (q ≫ p))

/-- The composite inverse-image comparison retains the original native Hom adjunction. -/
theorem abelianPullbackCompIso_homEquiv
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (pullback AddCommGrpCat.{u} (q ≫ p)).obj A ⟶ B) :
    (abelianPullbackCompAdjunction p q).homEquiv _ _
        ((abelianPullbackCompIso p q).hom.app A ≫ a) =
      (pullbackPushforwardAdjunction AddCommGrpCat.{u} (q ≫ p)).homEquiv _ _ a := by
  erw [(abelianPullbackCompAdjunction p q).homEquiv_naturality_right]
  rw [abelianPullbackCompIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_apply]

/-- The native free-open inverse-image comparison retains the original represented sections. -/
theorem openFreeAbelianPullbackIso_hom_sections (U : Opens X)
    (B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (openFreeAbelianFunctor Y).obj ((Opens.map p).obj U) ⟶ B) :
    openFreeAbelianHomEquiv X U ((pushforward AddCommGrpCat.{u} p).obj B)
        ((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).homEquiv _ _
          ((openFreeAbelianPullbackObjIso p U).hom ≫ a)) =
      openFreeAbelianHomEquiv Y ((Opens.map p).obj U) B a := by
  have h := openFreeAbelianPullbackHomEquiv_sections p U B
    ((openFreeAbelianPullbackObjIso p U).hom ≫ a)
  erw [openFreeAbelianPullbackHomEquiv_comp] at h
  rw [openFreeAbelianPullbackHomEquiv_hom, Category.id_comp] at h
  exact h.symm

/-- The original free-open comparisons compose through the canonical native inverse-image
comparison. Both inverse-image opens are the actual native preimages. -/
theorem openFreeAbelianPullbackIso_comp_hom (U : Opens X) :
    (pullback AddCommGrpCat.{u} q).map (openFreeAbelianPullbackObjIso p U).hom ≫
        (openFreeAbelianPullbackObjIso q ((Opens.map p).obj U)).hom =
      (abelianPullbackCompIso p q).hom.app ((openFreeAbelianFunctor X).obj U) ≫
        (openFreeAbelianPullbackObjIso (q ≫ p) U).hom := by
  apply ((abelianPullbackCompAdjunction p q).homEquiv _ _).injective
  apply (openFreeAbelianHomEquiv X U
    ((pushforward AddCommGrpCat.{u} (q ≫ p)).obj
      ((openFreeAbelianFunctor Z).obj ((Opens.map (q ≫ p)).obj U)))).injective
  conv_rhs => erw [abelianPullbackCompIso_homEquiv p q]
  have hcomp := openFreeAbelianPullbackIso_hom_sections (q ≫ p) U
    ((openFreeAbelianFunctor Z).obj ((Opens.map (q ≫ p)).obj U)) (𝟙 _)
  rw [Category.comp_id] at hcomp
  erw [hcomp]
  dsimp only [abelianPullbackCompAdjunction]
  erw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change openFreeAbelianHomEquiv X U _
      (((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).comp
        (pullbackPushforwardAdjunction AddCommGrpCat.{u} q)).homEquiv _ _
          ((pullback AddCommGrpCat.{u} q).map (openFreeAbelianPullbackObjIso p U).hom ≫
            (openFreeAbelianPullbackObjIso q ((Opens.map p).obj U)).hom)) = _
  rw [Adjunction.comp_homEquiv]
  change openFreeAbelianHomEquiv X U _
      ((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).homEquiv _ _
        ((pullbackPushforwardAdjunction AddCommGrpCat.{u} q).homEquiv _ _
          ((pullback AddCommGrpCat.{u} q).map (openFreeAbelianPullbackObjIso p U).hom ≫
            (openFreeAbelianPullbackObjIso q ((Opens.map p).obj U)).hom))) = _
  erw [(pullbackPushforwardAdjunction AddCommGrpCat.{u} q).homEquiv_naturality_left]
  erw [openFreeAbelianPullbackIso_hom_sections]
  have hq := openFreeAbelianPullbackIso_hom_sections q ((Opens.map p).obj U)
    ((openFreeAbelianFunctor Z).obj ((Opens.map q).obj ((Opens.map p).obj U))) (𝟙 _)
  rw [Category.comp_id] at hq
  exact hq

/-- The inverse free-open comparisons retain the same canonical composite inverse image. -/
theorem openFreeAbelianPullbackIso_comp_inv (U : Opens X) :
    (openFreeAbelianPullbackObjIso q ((Opens.map p).obj U)).inv ≫
        (pullback AddCommGrpCat.{u} q).map (openFreeAbelianPullbackObjIso p U).inv =
      (openFreeAbelianPullbackObjIso (q ≫ p) U).inv ≫
        (abelianPullbackCompIso p q).inv.app ((openFreeAbelianFunctor X).obj U) := by
  have h : (pullback AddCommGrpCat.{u} q).mapIso (openFreeAbelianPullbackObjIso p U) ≪≫
      openFreeAbelianPullbackObjIso q ((Opens.map p).obj U) =
    (abelianPullbackCompIso p q).app ((openFreeAbelianFunctor X).obj U) ≪≫
      openFreeAbelianPullbackObjIso (q ≫ p) U := by
    apply Iso.ext
    exact openFreeAbelianPullbackIso_comp_hom p q U
  exact congrArg Iso.inv h

end TopCat.Sheaf
