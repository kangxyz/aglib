/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GeneralHyperplane
public import Mathlib.Tactic.FinCases

/-! Focused consumer of the general hyperplane: one section of `O(1)` whose frame coefficients
are nonzerodivisors on the chart sections of finitely many coherent modules. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

/-- Three coherent modules on `P^n_k`, `k` infinite, have a common general hyperplane: one
section `s` of `O(1)` whose frame coefficients are nonzerodivisors on all their chart sections. -/
example (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (F G H : (ProjectiveSpace k (ULift.{u} (Fin (n + 1)))).Modules)
    (hF : affineLocallyFiniteType _ F) (hG : affineLocallyFiniteType _ G)
    (hH : affineLocallyFiniteType _ H) :
    ∃ s : (twistingSheaf k (ULift.{u} (Fin (n + 1))) ((1 : ℕ) : ℤ)).val.obj (op ⊤),
      ∀ (j : Fin 3) (i : ULift.{u} (Fin (n + 1)))
        (V : (ProjectiveSpace k (ULift.{u} (Fin (n + 1)))).Opens)
        (hV : V ≤ coordinateOpen k (ULift.{u} (Fin (n + 1))) i),
        IsSMulRegular Γ(![F, G, H] j, V)
          (frameCoefficient k (ULift.{u} (Fin (n + 1))) s i hV) :=
  exists_forall_frameCoefficient_isSMulRegular k _ ![F, G, H] (by
    intro j
    fin_cases j
    exacts [hF, hG, hH])

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_forall_frameCoefficient_isSMulRegular'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_forall_frameCoefficient_isSMulRegular
