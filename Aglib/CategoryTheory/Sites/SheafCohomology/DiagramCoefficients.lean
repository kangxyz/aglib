/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Coefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.DiagramTransfer

/-! # Coefficient squares on the native sheaf cohomology presheaves

The complete Ext-diagram coefficient law is stated at the literal native
cohomology-presheaf functors before a geometric site or pullback is substituted.
The source diagrams are exactly the native sheafified free representables.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v'}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf K AddCommGrpCat.{v'})]

local notation "FJ" =>
  (yoneda ⋙ Functor.obj (Functor.whiskeringRight Cᵒᵖ _ _) AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat)
local notation "FK" =>
  (yoneda ⋙ Functor.obj (Functor.whiskeringRight Dᵒᵖ _ _) AddCommGrpCat.free ⋙
    presheafToSheaf K AddCommGrpCat)

/-- The original exact Ext transfer respects coefficients on the literal native
cohomology presheaves, including the original target reindexing. -/
theorem cohomologyPresheaf_extDiagramMap_coefficients
    (L : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v'})
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (H : C ⥤ D) (e : FJ ⋙ L ≅ H ⋙ FK)
    {A A' : Sheaf J AddCommGrpCat.{v}} {B B' : Sheaf K AddCommGrpCat.{v'}}
    (a : L.obj A ⟶ B) (a' : L.obj A' ⟶ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : L.map f ≫ a' = a ≫ g) (n : ℕ) :
    (cohomologyPresheafFunctor J n).map f ≫ cohomologyPresheafTransfer J K L H e a' n =
      cohomologyPresheafTransfer J K L H e a n ≫
        Functor.whiskerLeft H.op ((cohomologyPresheafFunctor K n).map g) := by
  ext U x
  exact (DFunLike.congr_fun
    (L.extCoefficientTransfer_naturality (e.inv.app U.unop) a a' f g h n) x).symm

end CategoryTheory.Sheaf
