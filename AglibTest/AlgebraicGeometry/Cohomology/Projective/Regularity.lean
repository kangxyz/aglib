/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.CoordinateGeneration

/-! Focused consumer of Castelnuovo–Mumford regularity on actual polynomial projective space:
the definition uses the original `Sheaf.H` of the native tensor twist `O(m - q) ⊗ F`. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

example (R : Type u) [CommRing R] (ι : Type u) (F : (ProjectiveSpace R ι).Modules) (m : ℤ) :
    IsProjectiveRegular R ι F m ↔ ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (m - q))).obj F)) q) :=
  Iff.rfl

example (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    ∃ m : ℤ, IsProjectiveRegular R ι F m :=
  exists_isProjectiveRegular R ι n e F hF

example (R : Type u) [CommRing R] (ι : Type u) [Finite ι] (F : (ProjectiveSpace R ι).Modules) :
    CategoryTheory.Epi (coordinateMultiplicationSum R ι F) :=
  inferInstance

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_isProjectiveRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_isProjectiveRegular

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_coordinateMultiplicationSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_coordinateMultiplicationSum

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_rfl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_rfl

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_comm
