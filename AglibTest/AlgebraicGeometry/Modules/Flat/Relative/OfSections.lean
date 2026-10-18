/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.OfSections

/-! Focused consumer of relative flatness from flat affine sections (Nitsure,
arXiv:math/0504590v1, proof of Lemma 3.2, p. 15, last step), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- Over an affine base, relative flatness is flatness of all affine sections. -/
example {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) (M : X.Modules)
    [M.IsQuasicoherent] :
    Scheme.Modules.relativeFlat f M ↔ ∀ U : X.Opens, IsAffineOpen U →
      Module.Flat A ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U (by simp)).hom).obj (ModuleCat.of Γ(X, U) Γ(M, U))) :=
  Scheme.Modules.relativeFlat_iff_flat_affineOpen_sections f M

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_of_flat_affineOpen_sections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_of_flat_affineOpen_sections

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_flat_affineOpen_sections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_flat_affineOpen_sections
