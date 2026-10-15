/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Structural ring actions on native open cohomology

The existing coefficient multiplication acts on the native open-Ext groups
`Sheaf.H'`. Its action is explicit in the structural ring map and remains
compatible with the original restrictions and coefficient maps. There is no
quasicoherence, flatness or finiteness hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u})

/-- Global functions act on the unchanged native open-Ext groups by coefficient multiplication. -/
def moduleHPrimeGlobalScalars (M : X.Modules) (n : ℕ) (U : X.Opens) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) where
  toFun a := (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
    (moduleScalarOfGlobal X M a)).app (op U)).hom
  map_zero' := by
    ext x
    rw [moduleScalarOfGlobal_zero]
    change x.comp (Ext.mk₀ (0 : moduleAddSheaf X M ⟶ _)) (Nat.add_zero n) = 0
    rw [Ext.mk₀_zero, Ext.comp_zero]
  map_one' := by
    ext x
    rw [moduleScalarOfGlobal_one]
    change x.comp (Ext.mk₀ (𝟙 (moduleAddSheaf X M))) (Nat.add_zero n) = x
    exact Ext.comp_mk₀_id x
  map_add' a b := by
    ext x
    rw [moduleScalarOfGlobal_add]
    change x.comp (Ext.mk₀ (moduleScalarOfGlobal X M a + moduleScalarOfGlobal X M b))
      (Nat.add_zero n) = _
    rw [Ext.mk₀_add, Ext.comp_add]
    rfl
  map_mul' a b := by
    ext x
    rw [moduleScalarOfGlobal_mul]
    change x.comp (Ext.mk₀ (moduleScalarOfGlobal X M b ≫ moduleScalarOfGlobal X M a))
      (Nat.add_zero n) = (x.comp (Ext.mk₀ (moduleScalarOfGlobal X M b))
        (Nat.add_zero n)).comp (Ext.mk₀ (moduleScalarOfGlobal X M a)) (Nat.add_zero n)
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

variable {R : Type v} [CommRing R]

/-- The specified structural ring acts on the same native `Sheaf.H'` group. -/
abbrev moduleHPrimeModuleOfHom (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) (U : X.Opens) :
    Module R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :=
  Module.compHom _ ((moduleHPrimeGlobalScalars X M n U).comp α)

/-- The displayed open-cohomology scalar is the original coefficient map. -/
theorem moduleHPrimeModuleOfHom_smul (α : R →+* Γ(X, ⊤))
    (M : X.Modules) (n : ℕ) (U : X.Opens) (a : R)
    (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    letI := moduleHPrimeModuleOfHom X α M n U
    a • x = ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      (moduleScalarOfGlobal X M (α a))).app (op U) x := rfl

/-- Original coefficient maps on native open cohomology are linear over the structural ring. -/
def moduleHPrimeMapOfHom (α : R →+* Γ(X, ⊤)) {M N : X.Modules}
    (φ : M ⟶ N) (n : ℕ) (U : X.Opens) :
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom X α N n U
    Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U →ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X N) n U := by
  letI := moduleHPrimeModuleOfHom X α M n U
  letI := moduleHPrimeModuleOfHom X α N n U
  refine {
    __ := (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).app (op U)).hom
    map_smul' := fun a x => ?_ }
  change (x.comp (Ext.mk₀ (moduleScalarOfGlobal X M (α a))) (Nat.add_zero n)).comp
      (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) (Nat.add_zero n) =
    (x.comp (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) (Nat.add_zero n)).comp
      (Ext.mk₀ (moduleScalarOfGlobal X N (α a))) (Nat.add_zero n)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, moduleScalarOfGlobal_naturality]

/-- The actual restriction maps on native open cohomology are linear over the structural ring. -/
def moduleHPrimeRestrictionOfHom (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (i : U ⟶ V) :
    letI := moduleHPrimeModuleOfHom X α M n V
    letI := moduleHPrimeModuleOfHom X α M n U
    Sheaf.H'.{u + 1} (moduleAddSheaf X M) n V →ₗ[R]
      Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U := by
  letI := moduleHPrimeModuleOfHom X α M n V
  letI := moduleHPrimeModuleOfHom X α M n U
  refine {
    __ := ((moduleAddSheaf X M).cohomologyPresheaf n).map i.op |>.hom
    map_smul' := fun a x => ?_ }
  exact congrArg (fun k => k x)
    (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      (moduleScalarOfGlobal X M (α a))).naturality i.op).symm

/-- The native open-cohomology presheaf, retaining the displayed structural scalar action. -/
def moduleHPrimePresheaf (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj U := by
    letI := moduleHPrimeModuleOfHom X α M n U.unop
    exact ModuleCat.of R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U.unop)
  map {U V} i := by
    letI := moduleHPrimeModuleOfHom X α M n U.unop
    letI := moduleHPrimeModuleOfHom X α M n V.unop
    exact ModuleCat.ofHom (moduleHPrimeRestrictionOfHom X α M n i.unop)
  map_id U := by
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
    exact (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n).map_id U
  map_comp {U V W} i j := by
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
    exact (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n).map_comp i j

/-- Forgetting the displayed scalars gives exactly the original native cohomology presheaf. -/
def moduleHPrimePresheafForgetIso (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    moduleHPrimePresheaf X α M n ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ≅
      Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n :=
  Iso.refl _

/-- The enriched restriction is the original native restriction on elements. -/
theorem moduleHPrimePresheaf_map_apply (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : (moduleHPrimePresheaf X α M n).obj U) :
    (moduleHPrimePresheaf X α M n).map i x =
      (Sheaf.cohomologyPresheaf.{u + 1} (moduleAddSheaf X M) n).map i x := rfl

end AlgebraicGeometry.Scheme.Cohomology
