/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.InfiniteField

/-! Focused consumer of the hyperplane sections over an infinite field and of Mumford's bound
over an infinite field for a submodule of an ambient module (Nitsure, arXiv:math/0504590v1,
p. 10 and Thm 2.3, p. 11), with no remaining premise. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

/-- Hyperplane sections exist over an infinite field with finitely many coordinates. -/
example (k : Type u) [Field k] [Infinite k] (ι : Type u) [Finite ι] :
    HasHyperplaneSections k ι :=
  hasHyperplaneSections_of_infinite k ι

/-- No coordinate is needed: without coordinates there are no charts, and every morphism is
mono. -/
example (k : Type u) [Field k] [Infinite k] : HasHyperplaneSections k PEmpty.{u + 1} :=
  hasHyperplaneSections_of_infinite k _

/-- Mumford's bound over an infinite field for a submodule of an ambient module. -/
example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (F G : (ProjectiveSpace k ι).Modules) (j : F ⟶ G) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (hG : IsMumfordAmbient n p G)
    (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  isProjectiveRegular_mumfordBound_of_infinite n p e j hF hG a hχ

/--
info: 'AlgebraicGeometry.ProjectiveSpace.frameCoefficient_eq_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.frameCoefficient_eq_map

/--
info: 'AlgebraicGeometry.ProjectiveSpace.frameCoefficient_add'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.frameCoefficient_add

/--
info: 'AlgebraicGeometry.ProjectiveSpace.frameCoefficient_smul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.frameCoefficient_smul

/--
info: 'AlgebraicGeometry.ProjectiveSpace.frameCoefficient_coordinateSection'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.frameCoefficient_coordinateSection

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSectionsUp_of_infinite'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSectionsUp_of_infinite

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSections_of_infinite'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSections_of_infinite

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_of_infinite'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_of_infinite
