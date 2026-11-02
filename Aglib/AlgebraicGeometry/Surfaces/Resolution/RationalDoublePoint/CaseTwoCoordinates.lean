/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoCubic
public import Aglib.RingTheory.Blowup.DoubleLine.Coordinates

/-!
# Original Case-II coordinates and the genuine cubic

The full linear-square canonical kernel is normalized on actual original
maximal-ideal generators. Rationality then supplies normality of their literal
ordinary chart, and the existing algebra constructs the original nonzero cubic.
The initial linear-square classification remains an honest separate input.
-/

@[expose] public noncomputable section

open IsLocalRing Localization.Away.SaturatedChart

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- A genuine Case-II full kernel supplies actual normalized generators and
one true original cubic with nonzero residue. Neither the normalized kernel
nor the cubic is assumed as an additional geometric conclusion. -/
theorem exists_original_coordinates_cubic_of_linearSquare_kernel
    (hd : ringKrullDim A = 2) (hA : IsNagataRing.{u, 0} A)
    (hRat : NormalModificationH1Vanishing A) (hsing : ¬ IsRegularLocalRing A)
    (g : Fin 3 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i => (g i : A)) = maximalIdeal A)
    (L : MvPolynomial (Fin 3) (ResidueField A)) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    ∃ t s z : maximalIdeal A,
      maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A) ∧
        doubleLineChildCotangentKernel A ![s, z, t] =
          Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} ∧
        ∃ F : CubicRelation t s z, F.remainder = 0 ∧ F.coefficients.residueCubic ≠ 0 := by
  obtain ⟨t, s, z, hgen', hker'⟩ := exists_original_doubleLine_generators g hgen L hL hL0 hker
  refine ⟨t, s, z, hgen', hker', ?_⟩
  exact exists_original_cubic_of_singular_normalized_kernel A hd hA hRat hsing
    t s z hgen' hker'

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
