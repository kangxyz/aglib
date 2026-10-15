/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Scalars
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Native linear Ext for actual scheme module sheaves

The actual structural linear category gives Mathlib's native module structure on every
original `Ext(M,N,n)`, together with its existing linear coefficient maps and bilinear
Yoneda composition. The scalar is original source precomposition, equivalently original
target postcomposition. On the structure-module source this is exactly the existing
`unitMul` action. The canonical original-cohomology comparison is linear for the same
native Ext action, with its unchanged forward map.

No Ext module structure or Yoneda algebra is redefined here. The general Ext scalar
formulas permit independent structural-ring and scheme universes; the cohomology comparison
retains the existing common-universe structural-scalar interface.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type v} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- Native structural scalar multiplication on arbitrary original module Ext is source
precomposition with the original module-linear multiplication endomorphism. -/
theorem moduleExt_smul_precomp_of_hom (M N : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} M N n) :
    letI := moduleCategoryLinearOfHom X α
    r • x = (Ext.mk₀ (globalScalarEndomorphism X M (α r))).comp x (Nat.zero_add n) := by
  let := moduleCategoryLinearOfHom X α
  calc
    r • x = (r • Ext.mk₀ (𝟙 M)).comp x (Nat.zero_add n) := by
      rw [Ext.smul_comp, Ext.mk₀_id_comp]
    _ = (Ext.mk₀ (r • 𝟙 M)).comp x (Nat.zero_add n) := by rw [Ext.mk₀_smul]
    _ = _ := by rw [moduleCategoryLinearOfHom_smul_id]

/-- The same native scalar is target postcomposition with original module multiplication. -/
theorem moduleExt_smul_postcomp_of_hom (M N : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} M N n) :
    letI := moduleCategoryLinearOfHom X α
    r • x = x.comp (Ext.mk₀ (globalScalarEndomorphism X N (α r))) (Nat.add_zero n) := by
  let := moduleCategoryLinearOfHom X α
  rw [Ext.smul_eq_comp_mk₀, moduleCategoryLinearOfHom_smul_id]

/-- Original global multiplication commutes across arbitrary module-linear Ext classes. -/
theorem moduleExt_scalar_precomp_eq_postcomp (M N : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} M N n) :
    (Ext.mk₀ (globalScalarEndomorphism X M (α r))).comp x (Nat.zero_add n) =
      x.comp (Ext.mk₀ (globalScalarEndomorphism X N (α r))) (Nat.add_zero n) := by
  let := moduleCategoryLinearOfHom X α
  exact (moduleExt_smul_precomp_of_hom X α M N n r x).symm.trans
    (moduleExt_smul_postcomp_of_hom X α M N n r x)

/-- On the original structure-module source, native Ext scalars are precisely the existing
source `unitMul` precomposition, with no transferred action. -/
theorem moduleExt_native_smul_eq_unitMul (M : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) M n) :
    letI := moduleCategoryLinearOfHom X α
    r • x = (Ext.mk₀ (unitMul X (α r))).comp x (Nat.zero_add n) := by
  let := moduleCategoryLinearOfHom X α
  rw [moduleExt_smul_precomp_of_hom, globalScalarEndomorphism_unit]

/-- The existing explicit unit-source Ext action and the native linear-category Ext action
have exactly the same scalar operation on the same original Ext group. -/
theorem moduleExt_native_smul_eq_existing (M : X.Modules) (n : ℕ) (r : R)
    (x : Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) M n) :
    letI := moduleCategoryLinearOfHom X α
    r • x = (letI := moduleExtModuleOfHom X α M n; r • x) := by
  let := moduleCategoryLinearOfHom X α
  change r • x = (Ext.mk₀ (unitMul X (α r))).comp x (Nat.zero_add n)
  exact moduleExt_native_smul_eq_unitMul X α M n r x

/-- The unchanged canonical Ext/cohomology comparison with Mathlib's native source Ext
module structure coming from the actual structural linear category. -/
def moduleExtCohomologyLinearEquivOfCategory {A : Type u} [CommRing A]
    (β : A →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    letI := moduleCategoryLinearOfHom X β
    letI := moduleCohomologyModuleOfHom X β M n
    Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) M n ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleCategoryLinearOfHom X β
  letI := moduleCohomologyModuleOfHom X β M n
  refine {
    __ := moduleExtCohomologyAddEquiv X M n
    map_smul' := fun r x => ?_ }
  change moduleExtCohomologyMap X M n (r • x) =
    Sheaf.H.map (moduleScalarOfGlobal X M (β r)) n (moduleExtCohomologyMap X M n x)
  rw [moduleExt_native_smul_eq_unitMul]
  exact moduleExtCohomologyMap_unitMul X M n (β r) x

/-- Native linear enrichment leaves the original canonical forward map unchanged. -/
theorem moduleExtCohomologyLinearEquivOfCategory_apply {A : Type u} [CommRing A]
    (β : A →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) M n) :
    moduleExtCohomologyLinearEquivOfCategory X β M n x = moduleExtCohomologyMap X M n x := rfl

end AlgebraicGeometry.Scheme.Cohomology
