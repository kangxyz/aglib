/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.DiagramTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Coefficients
public import Aglib.Topology.Sheaves.FreeAbelianPullback.Composition
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Abelian

/-! # The original open-cohomology transfer on topological spaces

The actual inverse-image functor and its native open-free comparison are fixed
once at topological spaces, before specializing to a scheme's underlying map.
Coefficient squares and composition are proved at this same constructor and
its literal cohomology-presheaf endpoints. The underlying Ext transfer remains
the existing unique native site constructor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X Y Z : TopCat.{u}}

/-- The original inverse image, displayed at its actual site-sheaf category heads. -/
abbrev openCohomologyInverseImage (p : Y ⟶ X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  pullback AddCommGrpCat.{u} p

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} p).isLeftAdjoint

local instance (p : Y ⟶ X) : RepresentablyFlat (Opens.map p) :=
  flat_of_preservesFiniteLimits _

local instance (p : Y ⟶ X) : PreservesFiniteLimits (openCohomologyInverseImage p) := by
  change PreservesFiniteLimits ((Opens.map p).sheafPullback AddCommGrpCat.{u} _ _)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

local instance (p : Y ⟶ X) : (openCohomologyInverseImage p).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

/-- Native inverse image on the original cohomology presheaves of opens. -/
def openCohomologyMap (p : Y ⟶ X)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B) (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheaf.{w} A n ⟶
      (Opens.map p).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf.{w} B n :=
  CategoryTheory.Sheaf.cohomologyPresheafTransfer
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    (openCohomologyInverseImage p) (Opens.map p) (openFreeAbelianPullbackIso p) a n

/-- An original coefficient square gives the complete native open-presheaf square. -/
theorem openCohomologyMap_coefficients (p : Y ⟶ X)
    {A A' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (a' : (openCohomologyInverseImage p).obj A' ⟶ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : (openCohomologyInverseImage p).map f ≫ a' = a ≫ g) (n : ℕ) :
    (CategoryTheory.Sheaf.cohomologyPresheafFunctor.{w}
        (Opens.grothendieckTopology X) n).map f ≫ openCohomologyMap p a' n =
      openCohomologyMap p a n ≫ Functor.whiskerLeft (Opens.map p).op
        ((CategoryTheory.Sheaf.cohomologyPresheafFunctor.{w}
          (Opens.grothendieckTopology Y) n).map g) := by
  ext U x
  exact (DFunLike.congr_fun
    ((openCohomologyInverseImage p).extCoefficientTransfer_naturality
      ((openFreeAbelianPullbackIso p).inv.app U.unop) a a' f g h n) x).symm

/-- Successive original inverse-image maps compose through the original adjunction comparison. -/
theorem openCohomologyMap_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {C : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (b : (openCohomologyInverseImage q).obj B ⟶ C) (n : ℕ) :
    openCohomologyMap p a n ≫
        Functor.whiskerLeft (Opens.map p).op (openCohomologyMap q b n) =
      openCohomologyMap (q ≫ p)
        ((abelianPullbackCompIso p q).inv.app A ≫
          (openCohomologyInverseImage q).map a ≫ b) n := by
  ext U x
  exact DFunLike.congr_fun
    (Functor.extCoefficientTransfer_comp
      (openCohomologyInverseImage p) (openCohomologyInverseImage q)
      (openCohomologyInverseImage (q ≫ p)) (abelianPullbackCompIso p q).symm
      ((openFreeAbelianPullbackIso p).inv.app U.unop)
      ((openFreeAbelianPullbackIso q).inv.app ((Opens.map p).obj U.unop))
      ((openFreeAbelianPullbackIso (q ≫ p)).inv.app U.unop)
      (openFreeAbelianPullbackIso_comp_inv p q U.unop).symm a b n) x

end TopCat.Sheaf
