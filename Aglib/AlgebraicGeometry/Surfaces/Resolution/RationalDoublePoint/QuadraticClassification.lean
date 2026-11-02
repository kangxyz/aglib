/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ExceptionalHilbert.Projective
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.QuadraticClassification.Core

/-!
# Actual original quadratic alternatives from exceptional cohomology

The genuine full exceptional Hilbert function supplies the original generators
and entire quadratic kernel. Case I retains global homogeneous nonsquare
information; Case II constructs normalized original coordinates and one true
nonzero cubic. The inverse-line cohomology supplier remains explicit.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open Localization.Away Localization.Away.SaturatedChart

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

local instance exceptionalClassificationResidueField : Field (A ⧸ maximalIdeal A) :=
  Ideal.Quotient.field (maximalIdeal A)

local instance exceptionalClassificationCohomologyModule (hd : ringKrullDim A = 2) (n : ℕ) :
    Module (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val n) :=
  moduleCohomologyModule (Over.mk (exceptionalStructureMap A hd))
    (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val n

/-- Genuine original inverse-line cohomology gives the actual Case-I/Case-II
alternatives. The first branch retains the global homogeneous nonsquare
condition, not merely the predicate on one selected affine chart. -/
theorem exceptional_original_quadratic_alternatives
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A) (hsing : ¬ IsRegularLocalRing A)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd))
      (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (dualLineBundle (exceptionalCurve A hd) (exceptionalLine A hd)).val 1) = 1) :
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
  obtain ⟨t, g, hgen⟩ := exceptional_exists_three_generators_of_inverseLine_cohomology
    A hd hA hRat hJ
  exact exceptional_original_quadratic_alternatives_of_hilbert A hd hA hRat hsing t g hgen
    (exceptional_hilbert_of_inverseLine_cohomology A hd hA hRat hJ)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
