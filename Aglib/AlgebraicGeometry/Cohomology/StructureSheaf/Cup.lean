/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Affine

/-!
# Cup product on the original structure-sheaf cohomology

The existing canonical comparison identifies the original structure-sheaf
`Sheaf.H` with native module-linear Ext from the structure module to itself.
The product below is native Yoneda composition through that same comparison.
Its scalar action is the original structural field action, and its unit,
bilinearity, and associativity are proved from the existing Ext laws.

This file introduces no replacement cohomology or resolution. Signed
commutativity, geometric pullback compatibility, and Künneth are separate
properties and are not assumptions of the construction here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] (X : FScheme k)

local instance : HasExt.{u + 1} (SheafOfModules.{u} X.left.ringCatSheaf) :=
  SheafOfModules.hasExt X.left.ringCatSheaf

/-- The original canonical module-Ext comparison, specialized to the
structure module and the actual structural field action. -/
def structureExtLinearEquiv (n : ℕ) :
    letI := moduleCategoryLinearOfHom X.left (constants X)
    Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
        (SheafOfModules.unit X.left.ringCatSheaf) n ≃ₗ[k]
      structureCohomology k X n := by
  letI := moduleCategoryLinearOfHom X.left (constants X)
  exact (moduleExtCohomologyLinearEquivOfCategory X.left (constants X)
      (SheafOfModules.unit X.left.ringCatSheaf) n).trans
    (structureModuleCohomologyEquiv X n)

/-- This comparison has the unchanged canonical scalar-forgetting map. -/
theorem structureExtLinearEquiv_apply (n : ℕ)
    (x : Ext.{u + 1} (C := X.left.Modules) (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) n) :
    structureExtLinearEquiv X n x =
      moduleExtCohomologyMap X.left (SheafOfModules.unit X.left.ringCatSheaf) n x := rfl

/-- Cup product of the actual structure-sheaf cohomology classes,
bilinear over the original structural field action. -/
def structureCup {p q n : ℕ} (h : p + q = n) :
    structureCohomology k X p →ₗ[k] structureCohomology k X q →ₗ[k]
      structureCohomology k X n := by
  letI := moduleCategoryLinearOfHom X.left (constants X)
  exact ((Ext.bilinearCompOfLinear (C := X.left.Modules) k
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)
      (SheafOfModules.unit X.left.ringCatSheaf)
      (SheafOfModules.unit X.left.ringCatSheaf) p q n h).compl₁₂
    (structureExtLinearEquiv X p).symm.toLinearMap
    (structureExtLinearEquiv X q).symm.toLinearMap).compr₂
      (structureExtLinearEquiv X n).toLinearMap

theorem structureCup_apply {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k X q) :
    structureCup X h x y = structureExtLinearEquiv X n
      (((structureExtLinearEquiv X p).symm x).comp
        ((structureExtLinearEquiv X q).symm y) h) := rfl

@[simp]
theorem structureExtLinearEquiv_symm_cup {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k X q) :
    (structureExtLinearEquiv X n).symm (structureCup X h x y) =
      ((structureExtLinearEquiv X p).symm x).comp
        ((structureExtLinearEquiv X q).symm y) h := by
  rw [structureCup_apply, LinearEquiv.symm_apply_apply]

/-- The cup unit is the original identity endomorphism of the structure
module, through the same canonical cohomology comparison. -/
def structureCupUnit : structureCohomology k X 0 :=
  structureExtLinearEquiv X 0 (Ext.mk₀ (𝟙 (SheafOfModules.unit X.left.ringCatSheaf)))

/-- The original degree-zero section comparison sends the cup unit to
the global section one. -/
@[simp]
theorem structureH0Equiv_cupUnit :
    structureH0Equiv X (structureCupUnit X) = 1 := by
  exact moduleExtCohomologyMap_mk₀_sections X.left
    (SheafOfModules.unit X.left.ringCatSheaf) (𝟙 _)

@[simp]
theorem structureCup_unit_left {n : ℕ} (x : structureCohomology k X n) :
    structureCup X (Nat.zero_add n) (structureCupUnit X) x = x := by
  simp [structureCup_apply, structureCupUnit]

@[simp]
theorem structureCup_unit_right {n : ℕ} (x : structureCohomology k X n) :
    structureCup X (Nat.add_zero n) x (structureCupUnit X) = x := by
  simp [structureCup_apply, structureCupUnit]

/-- Associativity of the original cup product, with the displayed degree
identifications and no independent cohomology model. -/
theorem structureCup_assoc {p q r pq qr n : ℕ}
    (hpq : p + q = pq) (hqr : q + r = qr) (h : p + q + r = n)
    (x : structureCohomology k X p) (y : structureCohomology k X q)
    (z : structureCohomology k X r) :
    structureCup X (show pq + r = n by omega) (structureCup X hpq x y) z =
      structureCup X (show p + qr = n by omega) x (structureCup X hqr y z) := by
  apply (structureExtLinearEquiv X n).symm.injective
  simp only [structureExtLinearEquiv_symm_cup]
  exact Ext.comp_assoc _ _ _ hpq hqr h

/-- Scalars on the cup unit reproduce the given structural field action. -/
theorem structureCup_smul_unit_left {n : ℕ} (a : k)
    (x : structureCohomology k X n) :
    structureCup X (Nat.zero_add n) (a • structureCupUnit X) x = a • x := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, structureCup_unit_left]

/-- The structural scalar action also agrees with right multiplication
by the scalar multiple of the cup unit. -/
theorem structureCup_smul_unit_right {n : ℕ} (a : k)
    (x : structureCohomology k X n) :
    structureCup X (Nat.add_zero n) x (a • structureCupUnit X) = a • x := by
  rw [LinearMap.map_smul, structureCup_unit_right]

/-- Every geometric pullback preserves the original cup unit, including
the generally nonflat identity section of a group scheme. -/
@[simp]
theorem structureCohomologyPullbackLinear_cupUnit {Y : FScheme k} (f : X ⟶ Y) :
    structureCohomologyPullbackLinear f 0 (structureCupUnit Y) = structureCupUnit X := by
  apply (structureH0Equiv X).injective
  rw [structureH0Equiv_cupUnit]
  change Sheaf.H.equiv₀ (structureAddSheaf X.left) Limits.isTerminalTop
      (structureCohomologyPullback f.left 0 (structureCupUnit Y)) = (1 : Γ(X.left, ⊤))
  rw [structureCohomologyPullback_equiv₀]
  change f.left.appTop (structureH0Equiv Y (structureCupUnit Y)) = 1
  rw [structureH0Equiv_cupUnit, map_one]

end AlgebraicGeometry.Scheme.Cohomology
