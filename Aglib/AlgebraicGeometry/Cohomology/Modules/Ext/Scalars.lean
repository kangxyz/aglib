/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars

/-!
# Structural scalars on original module Ext and its cohomology comparison

Global functions act on module-linear Ext from the structure module by
precomposition with the original `unitMul` endomorphisms. The canonical
scalar-forgetting comparison is linear for this action and the existing
coefficient-multiplication action on additive `Sheaf.H`. The forward map
is unchanged; no module action is transported through a chosen equivalence.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u v

variable (X : Scheme.{u})

local instance : HasExt.{u + 1} (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.hasExt X.ringCatSheaf

local instance : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
  ⟨fun _ => inferInstance⟩

/-- Global functions act on actual structure-module Ext by original source precomposition. -/
def moduleExtGlobalScalars (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End
      (Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) where
  toFun a := (Ext.mk₀ (Scheme.Modules.unitMul X a)).precomp M (Nat.zero_add n)
  map_zero' := by
    ext x
    change (Ext.mk₀ (Scheme.Modules.unitMul X 0)).comp x (Nat.zero_add n) = 0
    rw [Scheme.Modules.unitMul_zero, Ext.mk₀_zero, Ext.zero_comp]
  map_one' := by
    ext x
    change (Ext.mk₀ (Scheme.Modules.unitMul X 1)).comp x (Nat.zero_add n) = x
    rw [Scheme.Modules.unitMul_one]
    exact Ext.mk₀_id_comp x
  map_add' a b := by
    ext x
    change (Ext.mk₀ (Scheme.Modules.unitMul X (a + b))).comp x (Nat.zero_add n) =
      (Ext.mk₀ (Scheme.Modules.unitMul X a)).comp x (Nat.zero_add n) +
        (Ext.mk₀ (Scheme.Modules.unitMul X b)).comp x (Nat.zero_add n)
    rw [Scheme.Modules.unitMul_add, Ext.mk₀_add, Ext.add_comp]
  map_mul' a b := by
    ext x
    change (Ext.mk₀ (Scheme.Modules.unitMul X (a * b))).comp x (Nat.zero_add n) =
      (Ext.mk₀ (Scheme.Modules.unitMul X a)).comp
        ((Ext.mk₀ (Scheme.Modules.unitMul X b)).comp x (Nat.zero_add n)) (Nat.zero_add n)
    rw [Scheme.Modules.unitMul_mul, ← Ext.mk₀_comp_mk₀]
    exact Ext.comp_assoc_of_second_deg_zero _ _ _ (Nat.zero_add n)

/-- A specified structural ring acts on the same original structure-module Ext group. -/
abbrev moduleExtModuleOfHom {R : Type v} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    Module R (Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :=
  Module.compHom _ ((moduleExtGlobalScalars X M n).comp α)

/-- The displayed source action is original precomposition with structural multiplication. -/
theorem moduleExtModuleOfHom_smul {R : Type v} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    letI := moduleExtModuleOfHom X α M n
    r • x = (Ext.mk₀ (Scheme.Modules.unitMul X (α r))).comp x (Nat.zero_add n) := rfl

/-- The existing coefficient multiplication is a natural endomorphism of the native
scalar-forgetting functor. -/
def moduleScalarOfGlobalNat (a : Γ(X, ⊤)) :
    SheafOfModules.toSheaf.{u} X.ringCatSheaf ⟶
      SheafOfModules.toSheaf.{u} X.ringCatSheaf where
  app M := moduleScalarOfGlobal X M a
  naturality := by
    intro M N f
    exact (moduleScalarOfGlobal_naturality X f a).symm

/-- Forgetting original structure-module multiplication gives original additive multiplication. -/
theorem moduleUnitMul_toAddSheaf (a : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (Scheme.Modules.unitMul X a) =
      moduleScalarOfGlobal X (SheafOfModules.unit X.ringCatSheaf) a := by
  ext U r
  change Γ(X, U.unop) at r
  change r * globalRestriction X U.unop a = globalRestriction X U.unop a * r
  exact mul_comm _ _

/-- The canonical Ext comparison intertwines original source multiplication with actual
coefficient multiplication on cohomology. -/
theorem moduleExtCohomologyMap_unitMul (M : X.Modules) (n : ℕ) (a : Γ(X, ⊤))
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    moduleExtCohomologyMap X M n
        ((Ext.mk₀ (Scheme.Modules.unitMul X a)).comp x (Nat.zero_add n)) =
      Sheaf.H.map (moduleScalarOfGlobal X M a) n (moduleExtCohomologyMap X M n x) := by
  have hn := Ext.mapExactFunctor_comp_mk₀_natTransApp x (moduleScalarOfGlobalNat X a)
  rw [moduleExtCohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, moduleUnitMul_toAddSheaf]
  change (Ext.mk₀ (moduleUnitIntegerMap X)).comp
      ((Ext.mk₀ ((moduleScalarOfGlobalNat X a).app (SheafOfModules.unit X.ringCatSheaf))).comp
        (x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) (Nat.zero_add n))
      (Nat.zero_add n) =
    ((Ext.mk₀ (moduleUnitIntegerMap X)).comp
      (x.mapExactFunctor (SheafOfModules.toSheaf.{u} X.ringCatSheaf)) (Nat.zero_add n)).comp
        (Ext.mk₀ ((moduleScalarOfGlobalNat X a).app M)) (Nat.add_zero n)
  rw [Ext.comp_assoc_of_third_deg_zero, hn]

/-- Original module-linear Ext computes original cohomology linearly over the specified
structural ring, with both original scalar actions. -/
def moduleExtCohomologyLinearEquiv {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    letI := moduleExtModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α M n
    Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleExtModuleOfHom X α M n
  letI := moduleCohomologyModuleOfHom X α M n
  refine {
    __ := moduleExtCohomologyAddEquiv X M n
    map_smul' := fun a x => ?_ }
  exact moduleExtCohomologyMap_unitMul X M n (α a) x

/-- The linear equivalence has exactly the original canonical Ext comparison as forward map. -/
theorem moduleExtCohomologyLinearEquiv_apply {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M n) :
    letI := moduleExtModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α M n
    moduleExtCohomologyLinearEquiv X α M n x = moduleExtCohomologyMap X M n x := rfl

end AlgebraicGeometry.Scheme.Cohomology
