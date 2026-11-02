/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.NormalizedRestrictionSquare

/-! # The original normalized scalar open-cohomology restriction square

Native spaces supply only their original free-open diagrams, inverse images,
coefficient arrows and preimage transports to the complete variable-category
Ext-diagram construction, together with their original coefficient actions.
All four native cohomology objects and transfers are constructed there, rather
than rebuilt in the Scheme specialization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u w

variable {X Y T W : TopCat.{u}}
  [HasExt.{max u w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{max u w} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
  [HasExt.{max u w} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
  [HasExt.{max u w} (CategoryTheory.Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u})]

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
abbrev openCohomologyNormalizedScalarRestrictionSquare
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
    (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (ρA : R →+* End A) (ρB : S →+* End B)
    (ρL : R →+* End L) (ρQ : S →+* End Q)
    (hρp : ∀ r : R, (openCohomologyInverseImage p).map (ρA r) ≫ φp =
      φp ≫ ρB (σ r))
    (hρa : ∀ s : S, (openCohomologyInverseImage a).map (ρB s) ≫ φa = φa ≫ ρQ s)
    (hρj : ∀ r : R, (openCohomologyInverseImage j).map (ρA r) ≫ φj = φj ≫ ρL r)
    (hρb : ∀ r : R, (openCohomologyInverseImage b).map (ρL r) ≫ φb =
      φb ≫ ρQ (σ r))
    (U : Opens X)
    (ha : (Opens.map a).obj ((Opens.map p).obj U) = ⊤)
    (hj : (Opens.map j).obj U = ⊤)
    {ZT : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    {ZW : CategoryTheory.Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}}
    (eT : (openFreeAbelianFunctor T).obj ⊤ ≅ ZT)
    (eW : (openFreeAbelianFunctor W).obj ((Opens.map b).obj ⊤) ≅ ZW)
    (sg : ZW ⟶ (openCohomologyInverseImage b).obj ZT)
    (hc : eW.inv ≫ (openFreeAbelianPullbackIso b).inv.app ⊤ =
      sg ≫ (openCohomologyInverseImage b).map eT.inv) := fun h =>
  (openCohomologyInverseImage p).extScalarNormalizedRestrictionSquare
    (openCohomologyInverseImage a) (openCohomologyInverseImage j)
    (openCohomologyInverseImage b)
    (openFreeAbelianFunctor X) (openFreeAbelianFunctor Y)
    (openFreeAbelianFunctor T) (openFreeAbelianFunctor W)
    (Opens.map p) (Opens.map a) (Opens.map j) (Opens.map b)
    (openFreeAbelianPullbackIso p) (openFreeAbelianPullbackIso a)
    (openFreeAbelianPullbackIso j) (openFreeAbelianPullbackIso b)
    φp φa φj φb n
    (σ := σ) (ρ₀ := ρA) (ρ₁ := ρB) (ρ₂ := ρL) (ρ₃ := ρQ)
    (hp := hρp) (ha := hρa) (hj := hρj) (hb := hρb)
    (τ := fun V =>
      (eqToHom (congrArg (fun f : W ⟶ X => (Opens.map f).obj V.unop) w).symm).op)
    (i := op U) (κJ := (eqToHom hj.symm).op) (κA := (eqToHom ha.symm).op)
    (hk := Subsingleton.elim _ _) (h := h)
    (e₂ := eT) (e₃ := eW) (sg := sg) (hc := hc)

end TopCat.Sheaf
