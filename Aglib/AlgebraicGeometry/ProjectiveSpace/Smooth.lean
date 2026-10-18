/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.PolynomialChart
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# The relative smooth dimension of polynomial projective space

The actual standard coordinate charts are polynomial spectra with one fewer
variable. Their structural maps are the original inclusions of coefficients.
Source locality proves the native smooth relative dimension, and its native
base-change property supplies the same fact for a Cartesian realization.
No condition on the commutative base ring is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

private theorem polynomialChart_smoothOfRelativeDimension
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (i : ι) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))) := by
  classical
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hcard : Fintype.card ι = n + 1 := by
    simpa using Fintype.card_congr e
  have hdim : Nat.card {j : ι // j ≠ i} = n := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hcard]
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (algebraMap R (MvPolynomial {j : ι // j ≠ i} R))
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr
  simpa only [hdim] using
    Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R {j : ι // j ≠ i}

/-- Polynomial projective n-space is smooth of relative dimension n over
every commutative ring, with the coordinate size supplied by e. -/
theorem toSpec_smoothOfRelativeDimension (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    SmoothOfRelativeDimension n (toSpec R ι) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n)
    (f := toSpec R ι)
    (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι)
  intro i
  let a := coordinateOpenIsoSpecPolynomial R ι i
  let : SmoothOfRelativeDimension n (eulerPolynomialChart R ι i ≫ toSpec R ι) := by
    rw [eulerPolynomialChart_toSpec]
    exact polynomialChart_smoothOfRelativeDimension R ι n e i
  have hc : SmoothOfRelativeDimension (0 + n)
      (a.hom ≫ (eulerPolynomialChart R ι i ≫ toSpec R ι)) := inferInstance
  have he : a.hom ≫ (eulerPolynomialChart R ι i ≫ toSpec R ι) =
      (coordinateOpen R ι i).ι ≫ toSpec R ι := by
    simp only [eulerPolynomialChart, ← Category.assoc, a, Iso.hom_inv_id, Category.id_comp]
  simpa only [Nat.zero_add, he] using hc

/-- A supplied Cartesian realization of polynomial projective n-space has
the native smooth relative dimension, without an additional smoothness input. -/
theorem smoothOfRelativeDimension_of_isPullback
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X Y : Scheme.{u}}
    (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of R)) (h : IsPullback a p (toSpec R ι) f) :
    SmoothOfRelativeDimension n p := by
  exact MorphismProperty.of_isPullback h (toSpec_smoothOfRelativeDimension R ι n e)

end AlgebraicGeometry.ProjectiveSpace
