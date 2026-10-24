/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleFullyFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Category

/-! # The original module-linear stalk inside an open immersion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- The original geometric point bijection as an isomorphism of fibre functors. -/
def geometricPointComapFiberIso :
    (pointSmallEtale (η ≫ f)).fiber ≅ siteBaseChange f ⋙ (pointSmallEtale η).fiber :=
  NatIso.ofComponents (fun U => (StalkInverseImage.pointEquiv f η U).toIso)
    (by
      intro U V g
      ext p
      exact StalkInverseImage.pointEquiv_naturality f η g p)

/-- Smallness of the actual comap point follows from the original geometric point. -/
theorem geometricPointComap_initiallySmall :
    InitiallySmall.{u} (siteBaseChange f ⋙ (pointSmallEtale η).fiber).Elements := by
  let e := (Functor.Elements.structuredArrowEquivalence
      (pointSmallEtale (η ≫ f)).fiber).trans
    ((StructuredArrow.mapNatIso (geometricPointComapFiberIso f η)).trans
      (Functor.Elements.structuredArrowEquivalence
        (siteBaseChange f ⋙ (pointSmallEtale η).fiber)).symm)
  exact initiallySmall_of_initial_of_initiallySmall e.functor

attribute [local instance] geometricPointComap_initiallySmall

local instance moduleStalkInsideRepresentablyFlat : RepresentablyFlat (siteBaseChange f) :=
  flat_of_preservesFiniteLimits (siteBaseChange f)

/-- The original geometric point identifies with the native site comap point. -/
def geometricPointComapIso :
    pointSmallEtale (η ≫ f) ≅
      (pointSmallEtale η).comap (siteBaseChange f) (siteBaseChange_coverPreserving f) where
  hom := ⟨(geometricPointComapFiberIso f η).inv⟩
  inv := ⟨(geometricPointComapFiberIso f η).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricPointComapFiberIso f η).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricPointComapFiberIso f η).inv_hom_id

variable (Λ : Type (u + 1)) [Ring Λ]

local instance moduleStalkInsideHasModuleLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

/-- The geometric-point comparison on actual module-valued sheaves. -/
def moduleValuedStalkInverseImageIso :
    (pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      moduleValuedInverseImage f Λ ⋙ (pointSmallEtale η).sheafFiber := by
  let e := geometricPointComapIso f η
  let e' : (pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      ((pointSmallEtale η).comap (siteBaseChange f)
        (siteBaseChange_coverPreserving f)).sheafFiber :=
    { hom := e.inv.sheafFiber
      inv := e.hom.sheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id]
        exact GrothendieckTopology.Point.Hom.sheafFiber_id _
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id]
        exact GrothendieckTopology.Point.Hom.sheafFiber_id _ }
  exact e' ≪≫ (pointSmallEtale η).sheafFiberComapIso (siteBaseChange f)
    (siteBaseChange_coverPreserving f) (ModuleCat.{u + 1} Λ)

/-- The original module-linear geometric stalk commutes with genuine native pullback. -/
def moduleStalkInverseImageIso :
    moduleGeometricStalk Λ (η ≫ f) ≅ moduleInverseImage f Λ ⋙ moduleGeometricStalk Λ η :=
  Functor.isoWhiskerLeft _ (moduleValuedStalkInverseImageIso f η Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageValuedIso Λ f).symm _ ≪≫
    Functor.associator _ _ _

variable [IsOpenImmersion f]

/-- Inside the open, extension by zero has exactly the original module-linear stalk. -/
def moduleLowerShriekStalkIso :
    moduleLowerShriek f Λ ⋙ moduleGeometricStalk Λ (η ≫ f) ≅ moduleGeometricStalk Λ η :=
  Functor.isoWhiskerLeft _ (moduleStalkInverseImageIso f η Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekInverseImageIso f Λ) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.EtaleCohomology
