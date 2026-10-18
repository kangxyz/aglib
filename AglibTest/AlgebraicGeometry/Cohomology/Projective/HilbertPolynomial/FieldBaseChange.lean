/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FieldBaseChange

/-! Focused consumer of the invariance of cohomology dimensions and Hilbert functions under field
extension. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Cohomology dimensions do not change under field extension. -/
example (k K : Type u) [Field k] [Field K] [Algebra k K] (ι : Type u) [Finite ι]
    (M : (ProjectiveSpace k ι).Modules) [M.IsQuasicoherent] (q : ℕ) :
    projectiveCohomologyDim K ι
        ((Scheme.Modules.pullback (ProjectiveSpace.map (algebraMap k K) ι)).obj M) q =
      projectiveCohomologyDim k ι M q :=
  projectiveCohomologyDim_pullback_map k K ι M q

/-- Hilbert functions do not change under a field map (axioms guarded in the `Fiber` test). -/
example (ι : Type u) [Finite ι] (k K : Type u) [Field k] [Field K] (ψ : k →+* K)
    (G : (ProjectiveSpace k ι).Modules) [G.IsQuasicoherent] (m : ℤ) :
    projectiveHilbertFunction K ι ((Scheme.Modules.pullback (ProjectiveSpace.map ψ ι)).obj G) m =
      projectiveHilbertFunction k ι G m :=
  congrFun (projectiveHilbertFunction_pullback_map ι ψ G) m

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_pullback_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_pullback_map
