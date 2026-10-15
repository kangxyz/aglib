/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual cohomology of arbitrary scheme module sheaves

For every module sheaf on an F-scheme, the underlying additive sheaf gives
its actual Zariski Sheaf.H in every nonnegative degree, in Type (u+1).
Scalars are the maps induced by multiplication by the structural constants.
The degree-zero comparison is the actual global-sections equivalence, with
scalar compatibility. Coefficient maps, their composition and isomorphism
invariance are constructed functorially. For the structure module this
agrees with structure-sheaf cohomology through a canonical linear equivalence.

There is no finiteness, Riemann–Roch, base-change or Picard premise in this
object layer. In particular this module imports neither a line-bundle degree
nor a representing Picard scheme. General coherent-cohomology properties
and applications are separate files.
Original application provenance K2-018#prop:k2018-arithmetic-characters, mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Modules` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
/-- The actual additive Zariski sheaf underlying a scheme module sheaf. -/
abbrev moduleAddSheaf (X : Scheme.{u}) (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M
variable {F : Type u} [Field F]
/-- Scalar multiplication as an endomorphism of the actual additive sheaf. -/
def moduleScalar (X : FScheme F) (M : X.left.Modules) (a : F) : moduleAddSheaf X.left M ⟶
  moduleAddSheaf X.left M where
  hom := {
    app := fun U ↦ AddCommGrpCat.ofHom {
      toFun := fun (x : M.val.obj U) ↦ constantSection X U.unop a • x
      map_zero' := smul_zero _
      map_add' := smul_add _ }
    naturality := by
      intro U V i
      ext x
      change M.val.obj U at x
      symm
      change M.val.map i (constantSection X U.unop a • x) =
        constantSection X V.unop a • M.val.map i x
      rw [M.val.map_smul]
      congr 1
      exact map_constantSection X i.unop a }

@[simp]
theorem moduleScalar_zero (X : FScheme F) (M : X.left.Modules) : moduleScalar X M 0 = 0 := by
  ext U x
  change M.val.obj U at x
  change constantSection X U.unop 0 • x = 0
  simp

@[simp]
theorem moduleScalar_one (X : FScheme F) (M : X.left.Modules) : moduleScalar X M 1 = 𝟙 _ := by
  ext U x
  change M.val.obj U at x
  change constantSection X U.unop 1 • x = x
  simp

@[simp]
theorem moduleScalar_add (X : FScheme F) (M : X.left.Modules) (a b : F) :
    moduleScalar X M (a + b) = moduleScalar X M a + moduleScalar X M b := by
  ext U x
  change M.val.obj U at x
  change constantSection X U.unop (a + b) • x =
    constantSection X U.unop a • x + constantSection X U.unop b • x
  simp [add_smul]

/-- Composition order agrees because the scalar ring is commutative. -/
theorem moduleScalar_mul (X : FScheme F) (M : X.left.Modules) (a b : F) :
    moduleScalar X M (a * b) = moduleScalar X M b ≫ moduleScalar X M a := by
  ext U x
  change M.val.obj U at x
  change constantSection X U.unop (a * b) • x =
    constantSection X U.unop a • (constantSection X U.unop b • x)
  simp [mul_smul]

/-- Actual Zariski Hⁿ, retaining the standard Ext universe. -/
abbrev moduleCohomology (F : Type u) [Field F] (X : FScheme F) (M : X.left.Modules) (n : ℕ) :
  Type (u + 1) :=
  Sheaf.H (moduleAddSheaf X.left M) n

/-- The action on cohomology induced functorially by structure-sheaf scalars. -/
def moduleCohomologyScalars (X : FScheme F) (M : X.left.Modules) (n : ℕ) : F →+* AddMonoid.End
  (moduleCohomology F X M n) where
  toFun a := Sheaf.H.map (moduleScalar X M a) n
  map_zero' := by
    ext x
    rw [moduleScalar_zero]
    change (Sheaf.functorH _ n).map 0 x = 0
    rw [Functor.map_zero]
    rfl
  map_one' := by
    ext x
    rw [moduleScalar_one]
    exact Sheaf.H.map_id_apply x
  map_add' a b := by
    ext x
    rw [moduleScalar_add]
    exact Sheaf.H.map_add_apply _ _ x
  map_mul' a b := by
    ext x
    rw [moduleScalar_mul]
    exact Sheaf.H.map_comp_apply _ _ x

/-- This module structure is constructed from the structural map, not supplied. -/
instance moduleCohomologyModule (X : FScheme F) (M : X.left.Modules) (n : ℕ) :
    Module F (moduleCohomology F X M n) :=
  Module.compHom _ (moduleCohomologyScalars X M n)

/-- Scalar multiplication is exactly the induced map on the actual sheaf Hⁿ. -/
theorem moduleCohomology_smul (X : FScheme F) (M : X.left.Modules) (n : ℕ) (a : F)
    (x : moduleCohomology F X M n) :
    a • x = Sheaf.H.map (moduleScalar X M a) n x := rfl

instance moduleGlobalSectionsModule (X : FScheme F) (M : X.left.Modules) :
    Module F (M.val.obj (op ⊤)) := Module.compHom _ (constants X)

/-- The structural-field-linear identification of degree-zero module cohomology with global
sections. -/
def moduleH0Equiv (X : FScheme F) (M : X.left.Modules) :
    moduleCohomology F X M 0 ≃ₗ[F] M.val.obj (op ⊤) where
  __ := Sheaf.H.equiv₀ (moduleAddSheaf X.left M) Limits.isTerminalTop
  map_smul' a x := by
    have hn := (Sheaf.H.equiv₀_naturality
      (Limits.isTerminalTop (α := X.left.Opens)) (moduleScalar X M a) x).symm
    change _ = constantSection X ⊤ a •
      (show M.val.obj (op ⊤) from Sheaf.H.equiv₀ (moduleAddSheaf X.left M)
        (Limits.isTerminalTop (α := X.left.Opens)) x) at hn
    change Sheaf.H.equiv₀ (moduleAddSheaf X.left M) (Limits.isTerminalTop (α := X.left.Opens))
      (Sheaf.H.map (moduleScalar X M a) 0 x) = constants X a •
        (show M.val.obj (op ⊤) from Sheaf.H.equiv₀ (moduleAddSheaf X.left M)
          (Limits.isTerminalTop (α := X.left.Opens)) x)
    simpa [constantSection] using hn

variable (X : FScheme F) {M N P : X.left.Modules}
/-- The map of underlying additive coefficient sheaves induced by a module-sheaf morphism. -/
def coefficientSheafMap (φ : M ⟶ N) : moduleAddSheaf X.left M ⟶ moduleAddSheaf X.left N :=
  (SheafOfModules.toSheaf X.left.ringCatSheaf).map φ

@[reassoc] theorem moduleScalar_naturality (φ : M ⟶ N) (a : F) :
    moduleScalar X M a ≫ coefficientSheafMap X φ =
      coefficientSheafMap X φ ≫ moduleScalar X N a := by
  ext U x
  change M.val.obj U at x
  exact ((φ.val.app U).hom.map_smul (constantSection X U.unop a) x)

/-- The structural-field-linear map on actual Sheaf.H induced by a module-sheaf morphism. -/
def moduleCohomologyMap (φ : M ⟶ N) (n : ℕ) :
    moduleCohomology F X M n →ₗ[F] moduleCohomology F X N n where
  __ := Sheaf.H.map (coefficientSheafMap X φ) n
  map_smul' a x := by
    change Sheaf.H.map (coefficientSheafMap X φ) n (Sheaf.H.map (moduleScalar X M a) n x) =
      Sheaf.H.map (moduleScalar X N a) n (Sheaf.H.map (coefficientSheafMap X φ) n x)
    rw [← Sheaf.H.map_comp_apply, moduleScalar_naturality, Sheaf.H.map_comp_apply]

@[simp] theorem moduleCohomologyMap_id (M : X.left.Modules) (n : ℕ) :
    moduleCohomologyMap X (𝟙 M) n = LinearMap.id := by
  ext x
  change Sheaf.H.map (𝟙 _) n x = x
  exact Sheaf.H.map_id_apply x

@[simp] theorem moduleCohomologyMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    moduleCohomologyMap X (φ ≫ ψ) n = (moduleCohomologyMap X ψ n).comp (moduleCohomologyMap X φ
      n) := by
  ext x
  change Sheaf.H.map (coefficientSheafMap X φ ≫ coefficientSheafMap X ψ) n x = _
  exact Sheaf.H.map_comp_apply _ _ x

/-- The structural-field-linear cohomology equivalence induced by a module-sheaf isomorphism. -/
def moduleCohomologyIso (e : M ≅ N) (n : ℕ) : moduleCohomology F X M n ≃ₗ[F] moduleCohomology F
  X N n := by
  haveI : IsIso (coefficientSheafMap X e.hom) := inferInstanceAs
    (IsIso ((SheafOfModules.toSheaf X.left.ringCatSheaf).map e.hom))
  exact LinearEquiv.ofBijective (moduleCohomologyMap X e.hom n)
    (ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ n).map (coefficientSheafMap X e.hom)))

/-- The scalar-compatible identification of unit-module cohomology with structure-sheaf
cohomology. -/
def structureModuleCohomologyEquiv (n : ℕ) :
    moduleCohomology F X (SheafOfModules.unit X.left.ringCatSheaf) n ≃ₗ[F] structureCohomology F
      X n where
  __ := AddEquiv.refl _
  map_smul' _ _ := rfl
end AlgebraicGeometry.Scheme.Cohomology
