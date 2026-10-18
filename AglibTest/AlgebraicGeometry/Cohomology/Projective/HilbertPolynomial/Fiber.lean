/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Fiber

/-! Focused consumer of the identification of the fibre cohomology of `P_A → Spec A` over a prime
`p` with the cohomology of the pulled-back module on `P_{κ(p)}` (Nitsure, arXiv:math/0504590v1,
Thm 3.7 (2), p. 17; proof of Thm 4.3, (A), pp. 20–21), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

/-- The fibre Euler characteristic of a twist over any ring is the fibre Hilbert function. -/
example {A : Type u} [CommRing A] (ι : Type u) (F : (ProjectiveSpace A ι).Modules) (m : ℤ)
    (p : PrimeSpectrum A) :
    moduleFiberEulerChar (toSpec A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) p =
      projectiveHilbertFunction p.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A p.asIdeal.ResidueField) ι)).obj F) m :=
  moduleFiberEulerChar_twistingTensor_toSpec ι F m p

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.finrank_moduleCohomology_eq_of_isIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.finrank_moduleCohomology_eq_of_isIso

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleFiberCohomologyDimension_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleFiberCohomologyDimension_toSpec

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleFiberEulerChar_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleFiberEulerChar_toSpec

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleFiberEulerChar_twistingTensor_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleFiberEulerChar_twistingTensor_toSpec

/-- Fibre Hilbert polynomials are unchanged by base change. -/
example {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (ι : Type u) [Finite ι]
    (F : (ProjectiveSpace A ι).Modules) [F.IsQuasicoherent] (t : PrimeSpectrum B) :
    projectiveHilbertPolynomial t.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap B t.asIdeal.ResidueField) ι)).obj
          ((Scheme.Modules.pullback (map φ ι)).obj F)) =
      projectiveHilbertPolynomial (PrimeSpectrum.comap φ t).asIdeal.ResidueField ι
        ((Scheme.Modules.pullback
          (map (algebraMap A (PrimeSpectrum.comap φ t).asIdeal.ResidueField) ι)).obj F) :=
  projectiveHilbertPolynomial_fiber_pullback_map ι φ F t

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_pullback_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_pullback_map

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_fiber_pullback_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_fiber_pullback_map

/--
info: 'AlgebraicGeometry.ProjectiveSpace.map_comp_map_eq_of_comp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.map_comp_map_eq_of_comp_eq
