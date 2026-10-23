/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Module.RingHom

/-!
# Scalar action on the original additive étale coefficient

Multiplication by actual global sections acts on the principal's additive
structure sheaf. The induced action on original cohomology, restricted through
the scheme's structural constants map, supplies the field-module structure
needed by the characteristic-primary curve argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

/-- The actual global-section restriction, with its precise ring-valued carrier displayed. -/
def structureSectionMap (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    Γ(X, ⊤) →+* (structurePresheaf X).obj U := U.unop.hom.appTop.hom

/-- Restriction of original global scalars commutes with the actual diagram maps. -/
theorem structureSectionMap_naturality (X : Scheme.{u})
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (a : Γ(X, ⊤)) :
    ((structurePresheaf X).map f).hom (structureSectionMap X U a) =
      structureSectionMap X V a := by
  let g := (Etale.forget X).map f.unop
  change (g.left ≫ ((Etale.forget X).obj U.unop).hom).appTop.hom a =
    ((Etale.forget X).obj V.unop).hom.appTop.hom a
  rw [Over.w]

/-- Actual multiplication by a global section on the original lifted coefficient. -/
def structureScalar (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    additiveStructureSheaf X ⟶ additiveStructureSheaf X where
  hom := {
    app U := AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom
      { toFun := fun (x : ((structurePresheaf X).obj U)) => structureSectionMap X U a * x
        map_zero' := mul_zero _
        map_add' := mul_add _ })
    naturality {U V} f := by
      ext x
      change ULift.{u + 1} ((structurePresheaf X).obj U) at x
      apply ULift.ext
      symm
      change ((structurePresheaf X).map f).hom
          (structureSectionMap X U a * x.down) =
        structureSectionMap X V a * ((structurePresheaf X).map f).hom x.down
      rw [map_mul]
      congr 1
      exact structureSectionMap_naturality X f a }

@[simp] theorem structureScalar_zero (X : Scheme.{u}) : structureScalar X 0 = 0 := by
  ext U x
  change ULift.{u + 1} ((structurePresheaf X).obj U) at x
  apply ULift.ext
  change structureSectionMap X U 0 * x.down = 0
  simp

@[simp] theorem structureScalar_one (X : Scheme.{u}) : structureScalar X 1 = 𝟙 _ := by
  ext U x
  change ULift.{u + 1} ((structurePresheaf X).obj U) at x
  apply ULift.ext
  change structureSectionMap X U 1 * x.down = x.down
  simp

@[simp] theorem structureScalar_add (X : Scheme.{u}) (a b : Γ(X, ⊤)) :
    structureScalar X (a + b) = structureScalar X a + structureScalar X b := by
  ext U x
  change ULift.{u + 1} ((structurePresheaf X).obj U) at x
  apply ULift.ext
  change structureSectionMap X U (a + b) * x.down =
    structureSectionMap X U a * x.down + structureSectionMap X U b * x.down
  simp [add_mul]

/-- Composition order matches multiplication on cohomology endomorphisms. -/
theorem structureScalar_mul (X : Scheme.{u}) (a b : Γ(X, ⊤)) :
    structureScalar X (a * b) = structureScalar X b ≫ structureScalar X a := by
  ext U x
  change ULift.{u + 1} ((structurePresheaf X).obj U) at x
  apply ULift.ext
  change structureSectionMap X U (a * b) * x.down =
    structureSectionMap X U a * (structureSectionMap X U b * x.down)
  simp [mul_assoc]

/-- The exact scalar/Frobenius square on the principal's original coefficient. -/
theorem structureScalar_frobenius (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) :
    structureScalar X a ≫ structureFrobenius X p hp hX =
      structureFrobenius X p hp hX ≫ structureScalar X (a ^ p) := by
  ext U x
  change ULift.{u + 1} ((structurePresheaf X).obj U) at x
  apply ULift.ext
  change (structureSectionMap X U a * x.down) ^ p =
    structureSectionMap X U (a ^ p) * x.down ^ p
  simp [mul_pow]

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The actual scalar action on original cohomology, in its independent Ext universe. -/
def structureCohomologyScalars (q : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H.{w} (additiveStructureSheaf X) q) where
  toFun a := Sheaf.H.map (structureScalar X a) q
  map_zero' := by
    ext x
    rw [structureScalar_zero]
    change (Sheaf.functorH _ q).map 0 x = 0
    rw [CategoryTheory.Functor.map_zero]
    rfl
  map_one' := by
    ext x
    rw [structureScalar_one]
    exact Sheaf.H.map_id_apply x
  map_add' a b := by
    ext x
    rw [structureScalar_add]
    exact Sheaf.H.map_add_apply _ _ x
  map_mul' a b := by
    ext x
    rw [structureScalar_mul]
    exact Sheaf.H.map_comp_apply _ _ x

variable {k : Type u} [Field k]

/-- Restriction through the actual structure morphism gives the canonical base-field action. -/
@[instance_reducible] def structureCohomologyModule (Y : FScheme k)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)] (q : ℕ) :
    Module k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
  Module.compHom _ ((structureCohomologyScalars Y.left q).comp (Scheme.constants Y))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
