/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Nonempty

/-! Focused consumer of the nonvanishing of Hilbert polynomials of nonempty closed subschemes of
`P^n_K` and its family forms (surjectivity of families with nonzero polynomial), with axiom
guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open scoped Polynomial

universe u

example {K : Type u} [Field K] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace K ι).IdealSheafData) :
    subschemeHilbertPolynomial ι K W ≠ 0 ↔ Nonempty W.subscheme :=
  subschemeHilbertPolynomial_ne_zero_iff ι n e W

example {K : Type u} [Field K] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (W : (ProjectiveSpace K ι).IdealSheafData) :
    subschemeHilbertPolynomial ι K W = 0 ↔ W = ⊤ :=
  subschemeHilbertPolynomial_eq_zero_iff ι n e W

example {K : Type u} [Field K] (ι : Type u) : subschemeHilbertPolynomial ι K ⊤ = 0 :=
  subschemeHilbertPolynomial_top ι

/-- A point of `Hilb^Φ(T)` with `Φ ≠ 0` is surjective over `T`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ g Z) (hΦ : Φ ≠ 0) :
    Surjective (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) :=
  hZ.surjective_of_ne_zero ι n e hΦ

/-- A point of `Hilb^Φ(T)` with a point has `Φ ≠ 0`. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} {Φ : ℚ[X]} {Z : (pullback (toSpec A ι) g).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ g Z) (z : Z.subscheme) : Φ ≠ 0 :=
  hZ.ne_zero_of_nonempty ι n e ⟨z⟩

/-- The chart fibre polynomial is nonzero exactly under the subscheme. -/
example {A : Type u} [CommRing A] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} (Z : (pullback (toSpec A ι) g).IdealSheafData) (t : T) :
    fiberHilbertPolynomialAt ι g Z.quotientModule t ≠ 0 ↔
      t ∈ Set.range (Z.subschemeι ≫ pullback.snd (toSpec A ι) g) :=
  fiberHilbertPolynomialAt_quotientModule_ne_zero_iff ι n e Z t

/--
info: 'AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.subschemeHilbertPolynomial_ne_zero_iff

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.surjective_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsHilbertFamily.surjective_of_ne_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_quotientModule_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.fiberHilbertPolynomialAt_quotientModule_eq_zero_iff
