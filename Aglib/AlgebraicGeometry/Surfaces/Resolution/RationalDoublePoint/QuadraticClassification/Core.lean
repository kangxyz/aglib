/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoCoordinates
public import Aglib.RingTheory.Blowup.QuadraticPresentation.Cases

/-!
# Original quadratic alternatives from the full original cone

One square/nonsquare split uses the actual entire quadratic kernel and original
generators. The genuine Hilbert-function producer is a thin caller. No initial
Hilbert data is needed when the actual full quadratic cone is already given.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

local instance exceptionalClassificationCoreComponentModule (r : ℕ) :
    Module (ResidueField A) (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r)

/-- Classify the actual nonzero homogeneous quadratic generating the entire
original cone kernel. Rationality constructs the true cubic in the square case. -/
theorem exceptional_original_quadratic_alternatives_of_quadratic_kernel
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A) (hsing : ¬ IsRegularLocalRing A)
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : A)) =
      maximalIdeal A)
    (q : MvPolynomial (Fin 3) (ResidueField A))
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q}) :
    (∃ (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
        (q : MvPolynomial (Fin 3) (ResidueField A)),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : A)) = maximalIdeal A ∧
        q ≠ 0 ∧ q.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q} ∧
        (t : A) ≠ 0 ∧ MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
        (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
        Nonempty (CaseOne.Presentation A t g (MvPolynomial.FirstCoordinate.dehom q)) ∧
        (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
          L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2) ∧
        (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
          l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q =
            MvPolynomial.C c * l ^ 2)) ∨
    (∃ t s z : maximalIdeal A,
      maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A) ∧
        doubleLineChildCotangentKernel A ![s, z, t] =
          Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} ∧
        ∃ F : CubicRelation t s z, F.remainder = 0 ∧ F.coefficients.residueCubic ≠ 0) := by
  classical
  have ht : (t : A) ≠ 0 := CaseOne.denominator_ne_zero_of_kernel t g q hq0 hq hker
  let a : Fin 6 → ResidueField A :=
    fun i => q.coeff (GradedAlgebra.TernaryQuadratic.exponent i)
  have hqa : q = GradedAlgebra.TernaryQuadratic.quadratic a :=
    GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq
  have ha : a ≠ 0 := by
    intro ha
    apply hq0
    rw [hqa, ha]
    simp only [GradedAlgebra.TernaryQuadratic.quadratic, Pi.zero_apply,
      map_zero, Finset.sum_const_zero]
  have hQ0 : MvPolynomial.FirstCoordinate.dehom q ≠ 0 := by
    rw [hqa]
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_ne_zero a ha
  have hdeg : (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 := by
    rw [hqa]
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree a
  have hD : Nonempty (CaseOne.Presentation A t g (MvPolynomial.FirstCoordinate.dehom q)) :=
    ⟨CaseOne.presentationOfKernel t g hgen q hker⟩
  by_cases hsquare : ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2
  · right
    obtain ⟨c, hc, L, hL, hL0, he⟩ := hsquare
    have hk : doubleLineChildCotangentKernel A (CaseOne.orderedGenerators t g) =
        Ideal.span {L ^ 2} := by
      change RingHom.ker (CaseOne.canonicalConeMap t g) = _
      rw [hker, he]
      exact Ideal.span_singleton_mul_left_unit
        ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C) _
    exact exists_original_coordinates_cubic_of_linearSquare_kernel A hd hA hRat hsing
      (CaseOne.orderedGenerators t g) hgen L hL hL0 hk
  · left
    refine ⟨t, g, q, hgen, hq0, hq, hker, ht, hQ0, hdeg, hD, hsquare, ?_⟩
    intro h
    exact hsquare ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq hq0).mp h)


/-- The existing genuine full-Hilbert producer feeds the same unique quadratic
classification on the displayed original generators. -/
theorem exceptional_original_quadratic_alternatives_of_hilbert
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A) (hsing : ¬ IsRegularLocalRing A)
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : A)) =
      maximalIdeal A)
    (hHilbert : ∀ r, Module.finrank (ResidueField A)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) = 2 * r + 1) :
    (∃ (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
        (q : MvPolynomial (Fin 3) (ResidueField A)),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : A)) = maximalIdeal A ∧
        q ≠ 0 ∧ q.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q} ∧
        (t : A) ≠ 0 ∧ MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
        (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
        Nonempty (CaseOne.Presentation A t g (MvPolynomial.FirstCoordinate.dehom q)) ∧
        (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
          L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2) ∧
        (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
          l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q =
            MvPolynomial.C c * l ^ 2)) ∨
    (∃ t s z : maximalIdeal A,
      maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A) ∧
        doubleLineChildCotangentKernel A ![s, z, t] =
          Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} ∧
        ∃ F : CubicRelation t s z, F.remainder = 0 ∧ F.coefficients.residueCubic ≠ 0) := by
  obtain ⟨q, hq0, hq, hker, _⟩ := CaseOne.exists_presentation_of_hilbert t g hgen hHilbert
  exact exceptional_original_quadratic_alternatives_of_quadratic_kernel
    A hd hA hRat hsing t g hgen q hq0 hq hker

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
