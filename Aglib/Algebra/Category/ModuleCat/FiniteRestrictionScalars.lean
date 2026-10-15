/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Finite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.Ring.Basic
/-! # Actual restriction of scalars along finite ring maps preserves finite modules. On noetherian
  rings it is exact for the genuine abelian structures. No surjectivity or full-faithfulness claim
  is made. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open ModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts
namespace ModuleCat.FiniteRestrictionScalars
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

/-- Actual restriction of scalars along a finite ring homomorphism. -/
def moduleRestriction : FGModuleCat.{u} S ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift _
    (forget₂ (FGModuleCat S) (ModuleCat S) ⋙ ModuleCat.restrictScalars φ.hom) (fun M => by
      change Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj M.obj)
      let : Algebra R S := φ.hom.toAlgebra
      let : Module.Finite R S := hφ
      let N := (ModuleCat.restrictScalars φ.hom).obj M.obj
      have : Module.Finite S N := M.property
      have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      exact Module.Finite.trans S N)

@[simp] theorem moduleRestriction_obj (M : FGModuleCat.{u} S) :
    ((moduleRestriction φ hφ).obj M).obj = (ModuleCat.restrictScalars φ.hom).obj M.obj := rfl

@[simp] theorem moduleRestriction_map {M N : FGModuleCat.{u} S} (f : M ⟶ N) :
    ((moduleRestriction φ hφ).map f).hom = (ModuleCat.restrictScalars φ.hom).map f.hom := rfl

instance moduleRestriction_additive : (moduleRestriction φ hφ).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

variable [IsNoetherianRing R] [IsNoetherianRing S]

instance moduleRestriction_preservesFiniteLimits : PreservesFiniteLimits (moduleRestriction φ hφ) :=
  by
  have : PreservesFiniteLimits
      (moduleRestriction φ hφ ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat S) (ModuleCat S) ⋙ ModuleCat.restrictScalars φ.hom)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (moduleRestriction φ hφ)
    (forget₂ (FGModuleCat R) (ModuleCat R))

instance moduleRestriction_preservesFiniteColimits : PreservesFiniteColimits (moduleRestriction φ
  hφ) := by
  have : PreservesFiniteColimits
      (moduleRestriction φ hφ ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat S) (ModuleCat S) ⋙ ModuleCat.restrictScalars φ.hom)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (moduleRestriction φ hφ)
    (forget₂ (FGModuleCat R) (ModuleCat R))

/-- The original scalar restriction on finite modules is exact. -/
def moduleRestrictionExact :
    ExactFunctor (finiteModuleExactStructure.{u,u} S) (finiteModuleExactStructure.{u,u} R) where
  toFunctor := moduleRestriction φ hφ
  map_conflation _ h := h.map_of_exact _

end ModuleCat.FiniteRestrictionScalars
