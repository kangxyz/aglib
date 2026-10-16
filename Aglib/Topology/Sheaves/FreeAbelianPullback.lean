/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-! # Inverse image of the native free abelian sheaf on an open

The native sheafified free abelian representable on an open pulls back to
the same construction on the inverse-image open. The comparison is natural
in the open and is normalized by the original sheaf pullback adjunction and
the original section-representing equivalence.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- The native free abelian sheaf on each representable open. -/
abbrev openFreeAbelianFunctor (X : TopCat.{u}) :
    Opens X ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight (Opens X)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The original free/sheafification adjunction identifies represented maps with sections. -/
def openFreeAbelianHomEquiv (X : TopCat.{u}) (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((openFreeAbelianFunctor X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u})).homEquiv
      _ _).trans yonedaEquiv)

/-- The original represented section equivalence is natural in the coefficient sheaf. -/
theorem openFreeAbelianHomEquiv_comp (X : TopCat.{u}) (U : Opens X)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (openFreeAbelianFunctor X).obj U ⟶ F) (b : F ⟶ G) :
    openFreeAbelianHomEquiv X U G (a ≫ b) =
      b.hom.app (op U) (openFreeAbelianHomEquiv X U F a) := by
  dsimp only [openFreeAbelianHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The original represented section equivalence is natural in the open. -/
theorem openFreeAbelianHomEquiv_naturality (X : TopCat.{u}) {U V : Opens X} (i : U ⟶ V)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (openFreeAbelianFunctor X).obj V ⟶ F) :
    openFreeAbelianHomEquiv X U F ((openFreeAbelianFunctor X).map i ≫ a) =
      F.obj.map i.op (openFreeAbelianHomEquiv X V F a) := by
  dsimp only [openFreeAbelianHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ i).symm

variable {X Y : TopCat.{u}} (p : Y ⟶ X)

/-- The native inverse-image adjunction identifies the two represented Hom functors. -/
def openFreeAbelianPullbackHomEquiv (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :
    ((pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj U) ⟶ F) ≃
      ((openFreeAbelianFunctor Y).obj ((Opens.map p).obj U) ⟶ F) :=
  (((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).homEquiv _ _).trans
    (openFreeAbelianHomEquiv X U ((pushforward AddCommGrpCat.{u} p).obj F))).trans
      (openFreeAbelianHomEquiv Y ((Opens.map p).obj U) F).symm

/-- The original inverse-image Hom equivalence is normalized by the original sections. -/
theorem openFreeAbelianPullbackHomEquiv_sections (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj U) ⟶ F) :
    openFreeAbelianHomEquiv Y ((Opens.map p).obj U) F
        (openFreeAbelianPullbackHomEquiv p U F a) =
      openFreeAbelianHomEquiv X U ((pushforward AddCommGrpCat.{u} p).obj F)
        (((pullbackPushforwardAdjunction AddCommGrpCat.{u} p).homEquiv _ _) a) :=
  Equiv.apply_symm_apply _ _

theorem openFreeAbelianPullbackHomEquiv_comp (U : Opens X)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj U) ⟶ F)
    (b : F ⟶ G) :
    openFreeAbelianPullbackHomEquiv p U G (a ≫ b) =
      openFreeAbelianPullbackHomEquiv p U F a ≫ b := by
  apply (openFreeAbelianHomEquiv Y ((Opens.map p).obj U) G).injective
  erw [openFreeAbelianPullbackHomEquiv_sections p U G (a ≫ b),
    openFreeAbelianHomEquiv_comp Y ((Opens.map p).obj U)
      (openFreeAbelianPullbackHomEquiv p U F a) b,
    openFreeAbelianPullbackHomEquiv_sections p U F a,
    Adjunction.homEquiv_naturality_right]
  rw [openFreeAbelianHomEquiv_comp]
  rfl

/-- The original open-free comparison, with both maps specified by represented sections. -/
def openFreeAbelianPullbackObjIso (U : Opens X) :
    (pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj U) ≅
      (openFreeAbelianFunctor Y).obj ((Opens.map p).obj U) where
  hom := (openFreeAbelianPullbackHomEquiv p U _).symm (𝟙 _)
  inv := openFreeAbelianPullbackHomEquiv p U _ (𝟙 _)
  hom_inv_id := by
    apply (openFreeAbelianPullbackHomEquiv p U _).injective
    rw [openFreeAbelianPullbackHomEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := openFreeAbelianPullbackHomEquiv_comp p U (𝟙 _)
      ((openFreeAbelianPullbackHomEquiv p U _).symm (𝟙 _))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

theorem openFreeAbelianPullbackHomEquiv_hom (U : Opens X) :
    openFreeAbelianPullbackHomEquiv p U _ (openFreeAbelianPullbackObjIso p U).hom = 𝟙 _ :=
  Equiv.apply_symm_apply _ _

/-- The original Hom comparison is normalized by precomposition with the constructed inverse. -/
theorem openFreeAbelianPullbackHomEquiv_eq (U : Opens X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj U) ⟶ F) :
    openFreeAbelianPullbackHomEquiv p U F a =
      (openFreeAbelianPullbackObjIso p U).inv ≫ a := by
  simpa only [Category.id_comp, openFreeAbelianPullbackObjIso] using
    openFreeAbelianPullbackHomEquiv_comp p U (𝟙 _) a

theorem openFreeAbelianPullbackHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (pullback AddCommGrpCat.{u} p).obj ((openFreeAbelianFunctor X).obj V) ⟶ F) :
    openFreeAbelianPullbackHomEquiv p U F
        ((pullback AddCommGrpCat.{u} p).map ((openFreeAbelianFunctor X).map i) ≫ a) =
      (openFreeAbelianFunctor Y).map ((Opens.map p).map i) ≫
        openFreeAbelianPullbackHomEquiv p V F a := by
  apply (openFreeAbelianHomEquiv Y ((Opens.map p).obj U) F).injective
  erw [openFreeAbelianPullbackHomEquiv_sections p U F
    ((pullback AddCommGrpCat.{u} p).map ((openFreeAbelianFunctor X).map i) ≫ a)]
  erw [openFreeAbelianHomEquiv_naturality Y ((Opens.map p).map i) F
    (openFreeAbelianPullbackHomEquiv p V F a)]
  erw [openFreeAbelianPullbackHomEquiv_sections p V F a,
    Adjunction.homEquiv_naturality_left]
  erw [openFreeAbelianHomEquiv_naturality X i]
  rfl

/-- Native inverse image carries the native open-free functor to inverse-image opens. -/
def openFreeAbelianPullbackIso :
    openFreeAbelianFunctor X ⋙ pullback AddCommGrpCat.{u} p ≅
      Opens.map p ⋙ openFreeAbelianFunctor Y := by
  refine NatIso.ofComponents (openFreeAbelianPullbackObjIso p) ?_
  intro U V i
  apply (openFreeAbelianPullbackHomEquiv p U _).injective
  change openFreeAbelianPullbackHomEquiv p U _
      ((pullback AddCommGrpCat.{u} p).map ((openFreeAbelianFunctor X).map i) ≫
        (openFreeAbelianPullbackObjIso p V).hom) =
    openFreeAbelianPullbackHomEquiv p U _ ((openFreeAbelianPullbackObjIso p U).hom ≫
      (openFreeAbelianFunctor Y).map ((Opens.map p).map i))
  erw [openFreeAbelianPullbackHomEquiv_naturality p i]
  erw [openFreeAbelianPullbackHomEquiv_comp p U (openFreeAbelianPullbackObjIso p U).hom]
  rw [openFreeAbelianPullbackHomEquiv_hom, openFreeAbelianPullbackHomEquiv_hom,
    Category.comp_id, Category.id_comp]

end TopCat.Sheaf
