/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.CoefficientSquare

/-! # The complete original open-cohomology coefficient square

Construct the four original cohomology presheaves, the two inverse-image maps,
and the two coefficient maps together with their commuting law before native
geometric specialization. Every edge is the original transfer or coefficient
map; this construction introduces neither a second cohomology model nor a
comparison hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

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

/-- The complete square of the original cohomology-presheaf coefficient maps
and inverse-image transfers, including its original commuting law. -/
def openCohomologyCoefficientSquare (p : Y ⟶ X)
    {A A' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (a : (openCohomologyInverseImage p).obj A ⟶ B)
    (a' : (openCohomologyInverseImage p).obj A' ⟶ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : (openCohomologyInverseImage p).map f ≫ a' = a ≫ g) (n : ℕ) :
    Square ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (openCohomologyInverseImage p).extDiagramCoefficientSquare
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (Opens.map p)
    (openFreeAbelianPullbackIso p) a a' f g h n

end TopCat.Sheaf
