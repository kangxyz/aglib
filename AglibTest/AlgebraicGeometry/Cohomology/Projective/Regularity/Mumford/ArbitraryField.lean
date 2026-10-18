/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.ArbitraryField

/-! Focused consumer of Mumford's bound over an arbitrary field (Nitsure, Thm 2.3), with no
premise, in Nitsure's normalization of the Hilbert polynomial. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

/-- Thm 2.3 for subsheaves of `O^p`, over every field. -/
example (k : Type u) [Field k] (ι : Type u) (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules)
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  isProjectiveRegular_mumfordBound_free n p e j hF a hχ

/-- Thm 2.3 for ideal sheaves, over every field, for instance a finite one. -/
example (n : ℕ) (F : (ProjectiveSpace (ZMod 2) (ULift.{0} (Fin (n + 1)))).Modules)
    (j : F ⟶ twistingSheaf (ZMod 2) (ULift.{0} (Fin (n + 1))) 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace (ZMod 2) (ULift.{0} (Fin (n + 1)))) F)
    (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction (ZMod 2) (ULift.{0} (Fin (n + 1))) F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular (ZMod 2) (ULift.{0} (Fin (n + 1))) F
      (MvPolynomial.eval a (mumfordBound n 1 (n + 1))) :=
  isProjectiveRegular_mumfordBound_ideal n Equiv.ulift j hF a hχ

/-- Thm 2.3 with the Hilbert coefficients produced: every coherent submodule of `O^p` is
`F_{p,n}(a)`-regular for its own coefficients `a`. -/
example (k : Type u) [Field k] (ι : Type u) (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules)
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    ∃ a : Fin (n + 1) → ℤ, (∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) ∧
      IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  exists_isProjectiveRegular_mumfordBound_free n p e j hF

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_free'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_free

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_ideal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_ideal

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_isProjectiveRegular_mumfordBound_free'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_isProjectiveRegular_mumfordBound_free
