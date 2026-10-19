/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FlatteningStratification.HilbertPolynomial

/-! Focused consumer of the strata `S_f` and of Theorem 4.3 (i) and (iii) (Nitsure,
arXiv:math/0504590v1, pp. 19 and 22–23), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- (i) and (iii) for one bound of the fibre statements of (B) and (C). -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) :
    ∃ N : ℕ, ∀ f ∈ Set.range (Scheme.Cohomology.fiberHilbertPolynomial F),
      Set.range (Scheme.Cohomology.hilbertPolynomialStratumι n e F hF N f) =
          {s : PrimeSpectrum A | Scheme.Cohomology.fiberHilbertPolynomial F s = f} ∧
        closure (Set.range (Scheme.Cohomology.hilbertPolynomialStratumι n e F hF N f)) ⊆
          ⋃ g ∈ {g ∈ Set.range (Scheme.Cohomology.fiberHilbertPolynomial F) |
              ∀ᶠ m : ℕ in Filter.atTop, f.eval (m : ℚ) ≤ g.eval (m : ℚ)},
            Set.range (Scheme.Cohomology.hilbertPolynomialStratumι n e F hF N g) := by
  obtain ⟨N, hN⟩ := Scheme.Cohomology.exists_isFiberBaseChangeBound n e F hF
  exact ⟨N, fun f hf => ⟨Scheme.Cohomology.range_hilbertPolynomialStratumι n e F hF hN f hf,
    Scheme.Cohomology.closure_range_hilbertPolynomialStratumι_subset n e F hF hN f hf⟩⟩

/-- Re-indexing by polynomials: `f ↦ (f(N), …, f(N + n))` is injective on the polynomials that
occur, for every `N`. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : Scheme.Modules.QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace A ι) F) (N : ℤ) :
    Set.InjOn (fun f : Polynomial ℚ => fun j : Fin (n + 1) => f.eval ((N + j : ℤ) : ℚ))
      (Set.range (Scheme.Cohomology.fiberHilbertPolynomial F)) :=
  Scheme.Cohomology.injOn_eval_projectiveHilbertPolynomial_fiber n e F hF N

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.iUnion_range_hilbertPolynomialStratumι_eq_univ_and_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.iUnion_range_hilbertPolynomialStratumι_eq_univ_and_pairwiseDisjoint

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.range_hilbertPolynomialStratumι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.range_hilbertPolynomialStratumι

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.closure_range_hilbertPolynomialStratumι_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.closure_range_hilbertPolynomialStratumι_subset

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_lift_hilbertPolynomialStratumι_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.injOn_eval_projectiveHilbertPolynomial_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.injOn_eval_projectiveHilbertPolynomial_fiber

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.natDegree_projectiveHilbertPolynomial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.natDegree_projectiveHilbertPolynomial_le

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sheafRank_directImageTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.sheafRank_directImageTwist

/--
info: 'AlgebraicGeometry.Scheme.Modules.mem_range_refinedJointRankStratumι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.mem_range_refinedJointRankStratumι_iff

/--
info: 'Polynomial.exists_eval_le_imp_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_eval_le_imp_eventually_le
