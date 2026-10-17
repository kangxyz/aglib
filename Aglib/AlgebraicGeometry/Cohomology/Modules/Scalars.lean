/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic

/-!
# Arbitrary structural ring actions on actual module-sheaf cohomology

A ring map to global functions acts on the original additive `Sheaf.H` by
multiplication on coefficients. The module structure is explicit in the map:
two different structural maps need not define the same action. Its degree-zero
comparison and coefficient maps are linear, and the existing field action is
the literal specialization to structural constants.

No quasicoherence, flatness, finiteness or Noetherianity is needed here. This
is the scalar layer for flat base change with arbitrary module coefficients.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u})

/-- Restriction of global functions to a specified open. -/
def globalRestriction (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

@[simp]
theorem globalRestriction_top_apply (a : Γ(X, ⊤)) : globalRestriction X ⊤ a = a := by
  change X.presheaf.map (𝟙 (op ⊤)) a = a
  rw [X.presheaf.map_id]
  rfl

@[simp]
theorem map_globalRestriction {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, ⊤)) :
    X.presheaf.map i.op (globalRestriction X V a) = globalRestriction X U a := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) a = _
  rw [← X.presheaf.map_comp]
  rfl

/-- Multiplication by a global function on the underlying additive module sheaf. -/
def moduleScalarOfGlobal (M : X.Modules) (a : Γ(X, ⊤)) :
    moduleAddSheaf X M ⟶ moduleAddSheaf X M where
  hom := {
    app := fun U ↦ AddCommGrpCat.ofHom {
      toFun := fun (x : M.val.obj U) ↦
        globalRestriction X U.unop a • x
      map_zero' := smul_zero _
      map_add' := smul_add _ }
    naturality := by
      intro U V i
      ext x
      change M.val.obj U at x
      symm
      change M.val.map i (globalRestriction X U.unop a • x) =
        globalRestriction X V.unop a • M.val.map i x
      rw [M.val.map_smul]
      congr 1
      exact map_globalRestriction X i.unop a }

@[simp]
theorem moduleScalarOfGlobal_zero (M : X.Modules) : moduleScalarOfGlobal X M 0 = 0 := by
  ext U x
  change M.val.obj U at x
  change globalRestriction X U.unop 0 • x = 0
  simp

@[simp]
theorem moduleScalarOfGlobal_one (M : X.Modules) :
    moduleScalarOfGlobal X M 1 = 𝟙 _ := by
  ext U x
  change M.val.obj U at x
  change globalRestriction X U.unop 1 • x = x
  simp

@[simp]
theorem moduleScalarOfGlobal_add (M : X.Modules) (a b : Γ(X, ⊤)) :
    moduleScalarOfGlobal X M (a + b) =
      moduleScalarOfGlobal X M a + moduleScalarOfGlobal X M b := by
  ext U x
  change M.val.obj U at x
  change globalRestriction X U.unop (a + b) • x =
    globalRestriction X U.unop a • x +
      globalRestriction X U.unop b • x
  simp [add_smul]

theorem moduleScalarOfGlobal_mul (M : X.Modules) (a b : Γ(X, ⊤)) :
    moduleScalarOfGlobal X M (a * b) =
      moduleScalarOfGlobal X M b ≫ moduleScalarOfGlobal X M a := by
  ext U x
  change M.val.obj U at x
  change globalRestriction X U.unop (a * b) • x =
    globalRestriction X U.unop a •
      (globalRestriction X U.unop b • x)
  simp [mul_smul]

/-- The action of global functions on the unchanged additive Zariski cohomology. -/
def moduleCohomologyGlobalScalars (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) where
  toFun a := Sheaf.H.map (moduleScalarOfGlobal X M a) n
  map_zero' := by
    ext x
    rw [moduleScalarOfGlobal_zero]
    change (Sheaf.functorH _ n).map 0 x = 0
    rw [Functor.map_zero]
    rfl
  map_one' := by
    ext x
    rw [moduleScalarOfGlobal_one]
    exact Sheaf.H.map_id_apply x
  map_add' a b := by
    ext x
    rw [moduleScalarOfGlobal_add]
    exact Sheaf.H.map_add_apply _ _ x
  map_mul' a b := by
    ext x
    rw [moduleScalarOfGlobal_mul]
    exact Sheaf.H.map_comp_apply _ _ x

variable {R : Type u} [CommRing R]

/-- The explicit scalar action associated to a specified map into global functions. -/
abbrev moduleCohomologyModuleOfHom (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    Module R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :=
  Module.compHom _ ((moduleCohomologyGlobalScalars X M n).comp α)

theorem moduleCohomologyModuleOfHom_smul (α : R →+* Γ(X, ⊤))
    (M : X.Modules) (n : ℕ) (a : R) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    letI := moduleCohomologyModuleOfHom X α M n
    a • x = Sheaf.H.map (moduleScalarOfGlobal X M (α a)) n x := rfl

@[reassoc]
theorem moduleScalarOfGlobal_naturality {M N : X.Modules} (φ : M ⟶ N)
    (a : Γ(X, ⊤)) :
    moduleScalarOfGlobal X M a ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map φ =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫ moduleScalarOfGlobal X N a := by
  ext U x
  change M.val.obj U at x
  exact (φ.val.app U).hom.map_smul
    (globalRestriction X U.unop a) x

/-- Coefficient maps are linear for the specified structural ring map. -/
def moduleCohomologyMapOfHom (α : R →+* Γ(X, ⊤)) {M N : X.Modules}
    (φ : M ⟶ N) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom X α N n
    Sheaf.H.{u + 1} (moduleAddSheaf X M) n →ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X N) n := by
  letI := moduleCohomologyModuleOfHom X α M n
  letI := moduleCohomologyModuleOfHom X α N n
  exact {
    __ := Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n
    map_smul' := fun a x ↦ by
      change Sheaf.H.map _ n (Sheaf.H.map (moduleScalarOfGlobal X M (α a)) n x) =
        Sheaf.H.map (moduleScalarOfGlobal X N (α a)) n (Sheaf.H.map _ n x)
      rw [← Sheaf.H.map_comp_apply, moduleScalarOfGlobal_naturality,
        Sheaf.H.map_comp_apply] }

/-- Degree-zero cohomology identifies with actual sections with the same ring action. -/
def moduleH0EquivOfHom (α : R →+* Γ(X, ⊤)) (M : X.Modules) :
    letI := moduleCohomologyModuleOfHom X α M 0
    letI : Module R (M.val.obj (op ⊤)) := Module.compHom _ α
    Sheaf.H.{u + 1} (moduleAddSheaf X M) 0 ≃ₗ[R] M.val.obj (op ⊤) := by
  let build (A : AddCommGrpCat.{u + 1}) (B : AddCommGrpCat.{u}) (sA : Module R A) (sB : Module R B)
      (e : A ≃+ B)
      (h : letI := sA; letI := sB; ∀ (a : R) (x : A), e (a • x) = a • e x) :
      letI := sA; letI := sB; A ≃ₗ[R] B := by
    letI := sA
    letI := sB
    exact { __ := e, map_smul' := h }
  refine build
    (AddCommGrpCat.of (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0))
    (AddCommGrpCat.of (M.val.obj (op ⊤)))
    (moduleCohomologyModuleOfHom X α M 0) (Module.compHom _ α)
    (Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop) ?_
  dsimp only
  intro a x
  have h := (Sheaf.H.equiv₀_naturality
    (Limits.isTerminalTop (α := X.Opens)) (moduleScalarOfGlobal X M (α a)) x).symm
  change Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop
    (Sheaf.H.map (moduleScalarOfGlobal X M (α a)) 0 x) =
      α a • (show M.val.obj (op ⊤) from
        Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop x)
  change Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop
    (Sheaf.H.map (moduleScalarOfGlobal X M (α a)) 0 x) =
      globalRestriction X ⊤ (α a) • (show M.val.obj (op ⊤) from
        Sheaf.H.equiv₀ (moduleAddSheaf X M) Limits.isTerminalTop x) at h
  simpa only [globalRestriction_top_apply] using h

open AlgebraicGeometry.Scheme.OverField

/-- The existing field scalar map is the specialization to the structural constants. -/
theorem moduleScalarOfGlobal_constants {K : Type u} [Field K] (Y : FScheme K)
    (M : Y.left.Modules) (a : K) :
    moduleScalarOfGlobal Y.left M (constants Y a) = moduleScalar Y M a := rfl

/-- The explicit arbitrary-ring action specializes to the original field action. -/
theorem moduleCohomologyModuleOfHom_constants {K : Type u} [Field K]
    (Y : FScheme K) (M : Y.left.Modules) (n : ℕ) :
    moduleCohomologyModuleOfHom Y.left (constants Y) M n =
      moduleCohomologyModule Y M n := rfl

end AlgebraicGeometry.Scheme.Cohomology
