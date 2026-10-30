/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.RingAction
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
    additiveStructureSheaf X ⟶ additiveStructureSheaf X :=
  CategoryTheory.Sheaf.RingAction.scalar (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a) a

@[simp] theorem structureScalar_zero (X : Scheme.{u}) : structureScalar X 0 = 0 :=
  CategoryTheory.Sheaf.RingAction.scalar_zero (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a)

@[simp] theorem structureScalar_one (X : Scheme.{u}) : structureScalar X 1 = 𝟙 _ :=
  CategoryTheory.Sheaf.RingAction.scalar_one (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a)

@[simp] theorem structureScalar_add (X : Scheme.{u}) (a b : Γ(X, ⊤)) :
    structureScalar X (a + b) = structureScalar X a + structureScalar X b :=
  CategoryTheory.Sheaf.RingAction.scalar_add (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a) a b

/-- Composition order matches multiplication on cohomology endomorphisms. -/
theorem structureScalar_mul (X : Scheme.{u}) (a b : Γ(X, ⊤)) :
    structureScalar X (a * b) = structureScalar X b ≫ structureScalar X a :=
  CategoryTheory.Sheaf.RingAction.scalar_mul (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a) a b

/-- The exact scalar/Frobenius square on the principal's original coefficient. -/
theorem structureScalar_frobenius (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (a : Γ(X, ⊤)) :
    structureScalar X a ≫ structureFrobenius X p hp hX =
      structureFrobenius X p hp hX ≫ structureScalar X (a ^ p) :=
  CategoryTheory.Sheaf.RingAction.scalar_frobenius
    (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a)
    p hp (primeCast_eq_zero_on_test X p hX) a

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The actual scalar action on original cohomology, in its independent Ext universe. -/
def structureCohomologyScalars (q : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H.{w} (additiveStructureSheaf X) q) :=
  CategoryTheory.Sheaf.RingAction.cohomologyScalars
    (structurePresheaf X) (Scheme.smallEtaleTopology X)
    (additiveStructurePresheaf_isSheaf X) Γ(X, ⊤) (structureSectionMap X)
    (fun {_ _} f a => structureSectionMap_naturality X f a) q

variable {k : Type u} [Field k]

/-- Restriction through the actual structure morphism gives the canonical base-field action. -/
@[instance_reducible] def structureCohomologyModule (Y : FScheme k)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)] (q : ℕ) :
    Module k (Sheaf.H.{w} (additiveStructureSheaf Y.left) q) :=
  Module.compHom _ ((structureCohomologyScalars Y.left q).comp (Scheme.constants Y))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
