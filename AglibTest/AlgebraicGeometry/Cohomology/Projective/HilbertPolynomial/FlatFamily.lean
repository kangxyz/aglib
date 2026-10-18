/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FlatFamily

/-! Focused consumer of the local constancy of fibre Hilbert functions and Hilbert polynomials of a
coherent, relatively flat module on `P^n_A` over a Noetherian ring `A` (Nitsure,
arXiv:math/0504590v1, Thm 3.7 (2), p. 17; proof of Thm 4.3, (A), pp. 20–21), with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

/-- For every `m`, `s ↦ χ(F_s(m))` is locally constant. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    (hflat : relativeFlat (toSpec A ι) F) (m : ℤ) :
    IsLocallyConstant (fun s : PrimeSpectrum A =>
      projectiveEulerChar s.asIdeal.ResidueField ι
        ((moduleTensorLeftFunctor (ProjectiveSpace s.asIdeal.ResidueField ι)
          (twistingSheaf s.asIdeal.ResidueField ι m)).obj
            ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F))) :=
  isLocallyConstant_projectiveHilbertFunction_fiber n e F hF hflat m

/-- The fibre Hilbert polynomial is locally constant. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    (hflat : relativeFlat (toSpec A ι) F) :
    IsLocallyConstant (fun s : PrimeSpectrum A =>
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F)) :=
  isLocallyConstant_projectiveHilbertPolynomial_fiber n e F hF hflat

/-- Over a connected base, all fibres have the same Hilbert polynomial. -/
example {A : Type u} [CommRing A] [IsNoetherianRing A] [ConnectedSpace (PrimeSpectrum A)]
    {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    (hflat : relativeFlat (toSpec A ι) F) (s t : PrimeSpectrum A) :
    projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) =
      projectiveHilbertPolynomial t.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A t.asIdeal.ResidueField) ι)).obj F) :=
  projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace n e F hF hflat s t

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_projectiveHilbertFunction_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_projectiveHilbertFunction_fiber

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_projectiveHilbertPolynomial_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.isLocallyConstant_projectiveHilbertPolynomial_fiber

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.exists_projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace
