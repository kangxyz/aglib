/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.RestrictionSquare

/-! # The complete original open-cohomology restriction square

Native spaces supply only their original free-open diagrams, inverse images,
coefficient arrows and preimage transports to the complete variable-category
Ext-diagram construction. All four native cohomology objects and transfers are
constructed there, rather than rebuilt in the Scheme specialization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u w

variable {X Y T W : TopCat.{u}}
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
  [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u})]

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

local instance {X Y : TopCat.{u}} (p : Y ⟶ X) :
    (openCohomologyInverseImage p).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction AddCommGrpCat.{u} p).isLeftAdjoint

local instance {X Y : TopCat.{u}} (p : Y ⟶ X) : RepresentablyFlat (Opens.map p) :=
  flat_of_preservesFiniteLimits _

local instance {X Y : TopCat.{u}} (p : Y ⟶ X) :
    PreservesFiniteLimits (openCohomologyInverseImage p) := by
  change PreservesFiniteLimits ((Opens.map p).sheafPullback AddCommGrpCat.{u} _ _)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

local instance {X Y : TopCat.{u}} (p : Y ⟶ X) : (openCohomologyInverseImage p).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Supply the original geometric and coefficient data to the full Ext square.
The remaining argument is the original comparison family, to be produced by
the native coefficient compatibility theorem at the consumer. -/
abbrev openCohomologyRestrictionSquare
    (a : W ⟶ Y) (b : W ⟶ T) (p : Y ⟶ X) (j : T ⟶ X)
    (w : a ≫ p = b ≫ j)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {L : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    {Q : CategoryTheory.Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}}
    (φp : (openCohomologyInverseImage p).obj A ⟶ B)
    (φa : (openCohomologyInverseImage a).obj B ⟶ Q)
    (φj : (openCohomologyInverseImage j).obj A ⟶ L)
    (φb : (openCohomologyInverseImage b).obj L ⟶ Q)
    (n : ℕ) (U : Opens X)
    (ha : (Opens.map a).obj ((Opens.map p).obj U) = ⊤)
    (hj : (Opens.map j).obj U = ⊤) :=
  (openCohomologyInverseImage p).extDiagramRestrictionSquare
    (openCohomologyInverseImage a) (openCohomologyInverseImage j)
    (openCohomologyInverseImage b)
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y)
    (openFreeAbelianFunctor T) (openFreeAbelianFunctor W)
    (Opens.map p) (Opens.map a) (Opens.map j) (Opens.map b)
    (openFreeAbelianPullbackIso p) (openFreeAbelianPullbackIso a)
    (openFreeAbelianPullbackIso j) (openFreeAbelianPullbackIso b)
    φp φa φj φb n
    (fun V => (eqToHom (congrArg (fun f : W ⟶ X => (Opens.map f).obj V.unop) w).symm).op)
    (op U) (eqToHom hj.symm).op (eqToHom ha.symm).op (Subsingleton.elim _ _)

end TopCat.Sheaf
