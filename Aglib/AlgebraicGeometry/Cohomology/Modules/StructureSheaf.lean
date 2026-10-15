/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.RingHom
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
# Actual Zariski structure-sheaf cohomology and scalar action

The cohomology object is mathlib's `Sheaf.H` of the additive structure sheaf,
with its canonical additive and scalar structures. Its universe is `u+1`, the standard Ext universe.
Scalar multiplication is induced by the structural map to `Spec F` and the
corresponding scalar endomorphism of the actual structure sheaf.

Original application provenance: K2-018#prop:k2018-arithmetic-characters, snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, lines 341–445 of
`research/exposes/K2/018/expose.tex`. Frozen engineering basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`, Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.StructureSheaf` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme
universe u

/-- The actual structure sheaf, with its additive-group values. -/
abbrev structureAddSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (sheafCompose _ (forget₂ RingCat AddCommGrpCat)).obj X.ringCatSheaf

/-- Explicit standard Ext universe, without a resizing assumption. -/
instance structureSheafHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {F : Type u} [Field F]

/-- Scalar multiplication as an endomorphism of the actual additive sheaf. -/
def structureScalar (X : FScheme F) (a : F) : structureAddSheaf X.left ⟶ structureAddSheaf
  X.left where
  hom := {
    app := fun U ↦ AddCommGrpCat.ofHom {
      toFun := fun (x : Γ(X.left, U.unop)) ↦ constantSection X U.unop a * x
      map_zero' := mul_zero _
      map_add' := mul_add _ }
    naturality := by
      intro U V i
      ext x
      change Γ(X.left, U.unop) at x
      symm
      change X.left.presheaf.map i (constantSection X U.unop a * x) =
        constantSection X V.unop a * X.left.presheaf.map i x
      rw [map_mul]
      congr 1
      exact map_constantSection X i.unop a }

@[simp]
theorem structureScalar_zero (X : FScheme F) : structureScalar X 0 = 0 := by
  ext U x
  change Γ(X.left, U.unop) at x
  change constantSection X U.unop 0 * x = 0
  simp

@[simp]
theorem structureScalar_one (X : FScheme F) : structureScalar X 1 = 𝟙 _ := by
  ext U x
  change Γ(X.left, U.unop) at x
  change constantSection X U.unop 1 * x = x
  simp

@[simp]
theorem structureScalar_add (X : FScheme F) (a b : F) :
    structureScalar X (a + b) = structureScalar X a + structureScalar X b := by
  ext U x
  change Γ(X.left, U.unop) at x
  change constantSection X U.unop (a + b) * x =
    constantSection X U.unop a * x + constantSection X U.unop b * x
  simp [add_mul]

/-- Composition order agrees because the scalar ring is commutative. -/
theorem structureScalar_mul (X : FScheme F) (a b : F) :
    structureScalar X (a * b) = structureScalar X b ≫ structureScalar X a := by
  ext U x
  change Γ(X.left, U.unop) at x
  change constantSection X U.unop (a * b) * x =
    constantSection X U.unop a * (constantSection X U.unop b * x)
  simp [mul_assoc]

/-- Actual Zariski H¹, retaining the standard Ext universe. -/
abbrev structureCohomology (F : Type u) [Field F] (X : FScheme F) (n : ℕ) : Type (u + 1) :=
  Sheaf.H (structureAddSheaf X.left) n

/-- The action on cohomology induced functorially by structure-sheaf scalars. -/
def cohomologyScalars (X : FScheme F) (n : ℕ) : F →+* AddMonoid.End (structureCohomology F X n)
  where
  toFun a := Sheaf.H.map (structureScalar X a) n
  map_zero' := by
    ext x
    rw [structureScalar_zero]
    change (Sheaf.functorH _ n).map 0 x = 0
    rw [Functor.map_zero]
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

/-- This module structure is constructed from the structural map, not supplied. -/
instance structureCohomologyModule (X : FScheme F) (n : ℕ) :
    Module F (structureCohomology F X n) :=
  Module.compHom _ (cohomologyScalars X n)

/-- Scalar multiplication is exactly the induced map on the actual sheaf Hⁿ. -/
theorem structureCohomology_smul (X : FScheme F) (n : ℕ) (a : F)
    (x : structureCohomology F X n) :
    a • x = Sheaf.H.map (structureScalar X a) n x := rfl

/-- Degree-one specialization of the actual structure-sheaf cohomology. -/
abbrev coherentH1 (F : Type u) [Field F] (X : FScheme F) : Type (u + 1) :=
  structureCohomology F X 1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
universe u
variable {F : Type u} [Field F]
/-- The module structure on global sections induced by the structural field constants. -/
abbrev globalSectionsModule (X : FScheme F) : Module F Γ(X.left, ⊤) :=
  (constants X).toModule
attribute [local instance] globalSectionsModule
/-- Degree-zero comparison with global sections, including scalar compatibility. -/
def structureH0Equiv (X : FScheme F) :
    structureCohomology F X 0 ≃ₗ[F] Γ(X.left, ⊤) where
  __ := Sheaf.H.equiv₀ (structureAddSheaf X.left) Limits.isTerminalTop
  map_smul' a x := by
    have hn := (Sheaf.H.equiv₀_naturality
      (Limits.isTerminalTop (α := X.left.Opens)) (structureScalar X a) x).symm
    change _ = constantSection X ⊤ a *
      (show Γ(X.left, ⊤) from Sheaf.H.equiv₀ (structureAddSheaf X.left) (Limits.isTerminalTop (α
        := X.left.Opens)) x) at hn
    change Sheaf.H.equiv₀ (structureAddSheaf X.left) (Limits.isTerminalTop (α := X.left.Opens))
      (Sheaf.H.map (structureScalar X a) 0 x) = constants X a *
        (show Γ(X.left, ⊤) from Sheaf.H.equiv₀ (structureAddSheaf X.left)
          (Limits.isTerminalTop (α := X.left.Opens)) x)
    simpa [constantSection] using hn
end AlgebraicGeometry.Scheme
