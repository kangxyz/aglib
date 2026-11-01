/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusEquation

/-!
# The zero-right-hand-side matrix Frobenius kernel

The fixed kernel is the zero-right-hand-side specialization of the actual
inhomogeneous equation algebra, not a separately isomorphic quotient. The
original fixed-point solution predicate and coordinate evaluation maps are
retained by the explicit zero-right-hand-side normalization. Finiteness still
requires generic shrinking; it does not follow from a free coefficient module.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.FrobeniusKernel

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
  (p : ℕ) (B : Matrix ι ι A)

/-- The zero-right-hand-side original equation. -/
abbrev equation := FrobeniusEquation.equation p B (0 : ι → A)

/-- Normalization recovers the original fixed-point polynomial. -/
theorem equation_eq (i : ι) :
    equation p B i = ∑ j, C (B i j) * X j ^ p - X i := by
  simp [FrobeniusEquation.equation]

/-- The actual ideal is the zero-right-hand-side member of the equation family. -/
abbrev equationIdeal := FrobeniusEquation.equationIdeal p B (0 : ι → A)

/-- The same literal quotient, with zero right-hand side. -/
abbrev CoordinateAlgebra := FrobeniusEquation.CoordinateAlgebra p B (0 : ι → A)

/-- The original coordinate class in that same quotient. -/
abbrev coordinate := FrobeniusEquation.coordinate p B (0 : ι → A)

variable {S : Type*} [CommRing S] [Algebra A S]

/-- The original fixed-point predicate, including for a zero test algebra. -/
def Solutions := {x : ι → S // ∀ i, ∑ j, algebraMap A S (B i j) * x j ^ p = x i}

/-- Zero-right-hand-side normalization leaves every coordinate unchanged. -/
def solutionsEquivZeroRhs :
    Solutions p B (S := S) ≃ FrobeniusEquation.Solutions p B (0 : ι → A) (S := S) :=
  Equiv.subtypeEquivRight fun _ => by
    simp only [Pi.zero_apply, map_zero, sub_eq_zero]

lemma aeval_equation (x : ι → S) (i : ι) :
    aeval x (equation p B i) = ∑ j, algebraMap A S (B i j) * x j ^ p - x i := by
  rw [equation_eq]
  simp

lemma coordinate_equation (i : ι) :
    ∑ j, algebraMap A (CoordinateAlgebra p B) (B i j) * coordinate p B j ^ p =
      coordinate p B i := by
  simpa only [Pi.zero_apply, map_zero, sub_eq_zero] using
    FrobeniusEquation.coordinate_equation p B (0 : ι → A) i

/-- The original map from the same quotient, through zero-RHS normalization. -/
def lift (x : Solutions p B (S := S)) : CoordinateAlgebra p B →ₐ[A] S :=
  FrobeniusEquation.lift p B (0 : ι → A) (solutionsEquivZeroRhs p B x)

@[simp]
lemma lift_coordinate (x : Solutions p B (S := S)) (i : ι) :
    lift p B x (coordinate p B i) = x.val i :=
  FrobeniusEquation.lift_coordinate p B (0 : ι → A) _ i

/-- The original coordinate evaluation equivalence, not an abstract algebra replacement. -/
def homEquivSolutions : (CoordinateAlgebra p B →ₐ[A] S) ≃ Solutions p B (S := S) :=
  (FrobeniusEquation.homEquivSolutions p B (0 : ι → A)).trans
    (solutionsEquivZeroRhs p B).symm

@[simp]
lemma homEquivSolutions_apply (h : CoordinateAlgebra p B →ₐ[A] S) (i : ι) :
    (homEquivSolutions p B h).val i = h (coordinate p B i) := rfl

variable {T : Type*} [CommRing T] [Algebra A T]

/-- Original solutions are transported by the actual target algebra map. -/
def mapSolutions (f : S →ₐ[A] T) (x : Solutions p B (S := S)) : Solutions p B (S := T) :=
  ⟨fun i => f (x.val i), fun i => by
    have hi := congrArg f (x.property i)
    simpa only [map_sum, map_mul, map_pow, AlgHom.commutes] using hi⟩

/-- Naturality remains literal postcomposition on the original quotient maps. -/
theorem homEquivSolutions_naturality (f : S →ₐ[A] T)
    (h : CoordinateAlgebra p B →ₐ[A] S) :
    homEquivSolutions p B (f.comp h) = mapSolutions p B f (homEquivSolutions p B h) := rfl

/-- The same native derivative formula at zero right-hand side. -/
lemma pderiv_equation (hp : (p : A) = 0) (i j : ι) :
    pderiv j (equation p B i) = -pderiv j (X i : MvPolynomial ι A) :=
  FrobeniusEquation.pderiv_equation p B (0 : ι → A) hp i j

/-- Etaleness is inherited from the original complete inhomogeneous construction. -/
theorem etale (hp : (p : A) = 0) : Algebra.Etale A (CoordinateAlgebra p B) :=
  FrobeniusEquation.etale p B (0 : ι → A) hp

end Algebra.FrobeniusKernel
