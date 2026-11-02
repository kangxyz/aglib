/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer
public import Aglib.Topology.Sheaves.Cech.Resolution
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.RestrictionCoefficientSquare

/-! # Native inputs for the complete open-restriction coefficient square

The original free-open and constant-integer objects, actual inverse image and
chosen top-free comparison are supplied to the complete variable-Ext
construction. No native Ext maps or naturality squares are rebuilt here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u w

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

/-- The original top comparison and coefficient data supply the same complete
Ext square. The remaining argument is the original open-comparison law. -/
abbrev openCohomologyRestrictionCoefficientSquare (p : Y ⟶ X)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (φ : (openCohomologyInverseImage p).obj A ⟶ B)
    (φ' : (openCohomologyInverseImage p).obj A ⟶ B') (ψ : B ⟶ B')
    (hφ : φ' = φ ≫ ψ) (n : ℕ) (U : Opens X) (hU : (Opens.map p).obj U = ⊤)
    (openMap : CategoryTheory.Sheaf.H'.{w} A n U ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{w} B n)) :=
  (openCohomologyInverseImage p).extDiagramOpenRestrictionCoefficientSquare
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y) (Opens.map p)
    (openFreeAbelianPullbackIso p) φ φ' ψ hφ n (op U) (op ⊤)
    (eqToHom hU.symm).op
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (Cech.additiveOpenTopIsoInteger Y) openMap

end TopCat.Sheaf
