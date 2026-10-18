/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Finiteness

/-! Focused consumer of the finiteness of the set of fibre Hilbert polynomials of a coherent module
on `P^n_A` over a Noetherian ring `A`, flat or not (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3, (A), pp. 20–21), and of generic flatness after base change to a basic open of a
Noetherian domain (Thm 4.2, p. 19), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Only finitely many Hilbert polynomials occur among the fibres of a coherent module. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) :
    (Set.range fun s : PrimeSpectrum A =>
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj
          F)).Finite :=
  finite_range_projectiveHilbertPolynomial_fiber n e F hF

/-- Over a Noetherian domain, the base change to some basic open `D(a)`, `a ≠ 0`, is flat. -/
example {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B] {ι : Type u} [Finite ι]
    (G : (ProjectiveSpace B ι).Modules) (hG : affineLocallyFiniteType (ProjectiveSpace B ι) G) :
    ∃ a : B, a ≠ 0 ∧ relativeFlat (toSpec (Localization.Away a) ι)
      ((Scheme.Modules.pullback (map (algebraMap B (Localization.Away a)) ι)).obj G) :=
  exists_ne_zero_relativeFlat_pullback_away G hG

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.finite_range_projectiveHilbertPolynomial_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.finite_range_projectiveHilbertPolynomial_fiber

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.finite_range_projectiveHilbertPolynomial_fiber_of_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.finite_range_projectiveHilbertPolynomial_fiber_of_relativeFlat

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_ne_zero_relativeFlat_pullback_away' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_ne_zero_relativeFlat_pullback_away
