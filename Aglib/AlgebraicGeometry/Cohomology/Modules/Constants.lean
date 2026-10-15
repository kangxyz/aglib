/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Structural constants on field schemes

The canonical ring map from the base field to global sections comes from the
actual structural morphism and Gamma-Spec isomorphism. Its open restrictions
commute with restriction. No cohomology, properness or finiteness is assumed.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.StructureSheaf` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The constants, constantSection and
  map_constantSection declarations only.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme
universe u
variable {F : Type u} [Field F]

/-- The canonical constants map induced by the actual structural morphism. -/
def constants (X : FScheme F) : F →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom

/-- Restriction of a constant to an arbitrary Zariski open. -/
def constantSection (X : FScheme F) (U : X.left.Opens) : F →+* Γ(X.left, U) :=
  (X.left.presheaf.map (homOfLE le_top).op).hom.comp (constants X)

@[simp]
theorem map_constantSection (X : FScheme F) {U V : X.left.Opens} (i : U ⟶ V) (a : F) :
    X.left.presheaf.map i.op (constantSection X V a) = constantSection X U a := by
  change (X.left.presheaf.map (homOfLE le_top).op ≫ X.left.presheaf.map i.op)
    (constants X a) = _
  rw [← X.left.presheaf.map_comp]
  rfl

end AlgebraicGeometry.Scheme
