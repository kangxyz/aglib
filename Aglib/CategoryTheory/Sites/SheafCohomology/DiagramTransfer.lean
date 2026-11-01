/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # The original Ext transfer on native cohomology presheaves

The original Ext-diagram constructor is given its literal native sheaf-cohomology
source and target before substituting a geometric site. No cohomology object,
free-representable comparison, or transfer map is replaced.
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

/-- The same exact Ext-diagram map, with the literal native cohomology-presheaf
source and original reindexed target. -/
def cohomologyPresheafTransfer
    (L : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v'})
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (H : C ⥤ D) (e : FJ ⋙ L ≅ H ⋙ FK)
    {A : Sheaf J AddCommGrpCat.{v}} {B : Sheaf K AddCommGrpCat.{v'}}
    (a : L.obj A ⟶ B) (n : ℕ) :
    cohomologyPresheaf.{w} A n ⟶ H.op ⋙ cohomologyPresheaf.{w} B n :=
  L.extDiagramMap FJ (H ⋙ FK) e a n

end CategoryTheory.Sheaf
