/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Normality
public import Aglib.AlgebraicGeometry.Blowup.Arc
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Chart
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Actual rational blowup charts and their original nonzero cubics

Rationality supplies normality of the ordinary blowup, hence integral
closedness of its literal saturated charts. The existing double-line
algebra then constructs a true original cubic with nonzero residue.
The normalized full canonical tangent kernel remains an explicit input;
this leaf does not assert that its actual coordinate normalization has
already been constructed from an arbitrary double-line equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- Integral closedness of the original saturated ordinary chart follows
from rationality on the actual global blowup, without completing its rings. -/
theorem ordinary_saturatedChart_isIntegrallyClosed (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (t : maximalIdeal A) (ht : (t : A) ≠ 0) :
    IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A)) := by
  let S := saturatedChart A (maximalIdeal A) (t : A)
  let : IsDomain (Localization.Away (t : A)) := Localization.Away.isDomain ht
  let : IsDomain S := inferInstance
  let j : Spec (.of S) ⟶ source A hd :=
    (Blowup.Arc.atlasChartWitness (maximalIdeal A) (datum A) t).val
  let : IsOpenImmersion j :=
    (Blowup.Arc.atlasChartWitness (maximalIdeal A) (datum A) t).property.1
  apply IsIntegrallyClosed.of_isLocalization_maximal
    (fun (P : Ideal S) [P.IsMaximal] => Localization.AtPrime P)
  intro P hP
  let q : Spec (.of S) := ⟨P, hP.isPrime⟩
  let : IsIntegrallyClosed ((source A hd).presheaf.stalk (j q)) :=
    (ordinary_normalStalks A hd hA hRat (j q)).2
  let e := asIso (j.stalkMap q) ≪≫ Blowup.Arc.spectrumStalkIso (.of S) q
  exact IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv

/-- The normalized original full tangent kernel and actual rationality
produce one true original cubic with nonzero original residue polynomial.
No ambient hypersurface or coefficient-field section is introduced. -/
theorem exists_original_cubic_of_normalized_kernel (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (t s z : maximalIdeal A) (ht : (t : A) ≠ 0)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    ∃ F : CubicRelation t s z, F.remainder = 0 ∧ F.coefficients.residueCubic ≠ 0 := by
  let : IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A)) :=
    ordinary_saturatedChart_isIntegrallyClosed A hd hA hRat t ht
  let E := DoubleLinePresentation.ofKernel t s z hgen hker
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, c0, c1, d0, hrel, hne⟩ :=
    exists_original_cubic_relation_nonzero t s z ht hgen
      E.equivalence E.parameter E.square
  let C : CubicCoefficients A := ⟨a0, a1, a2, a3, b0, b1, b2, c0, c1, d0⟩
  let F : CubicRelation t s z := ⟨C, 0, Ideal.zero_mem _, by
    simpa only [C, CubicCoefficients.value, add_zero] using hrel⟩
  exact ⟨F, rfl, hne⟩

/-- At an actual singular surface point, the original three-generator row
already makes the chosen parameter nonzero. The cubic therefore needs no
extra nonvanishing hypothesis on that original element. -/
theorem exists_original_cubic_of_singular_normalized_kernel (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (hsing : ¬ IsRegularLocalRing A) (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2}) :
    ∃ F : CubicRelation t s z, F.remainder = 0 ∧ F.coefficients.residueCubic ≠ 0 := by
  have ht : (t : A) ≠ 0 := by
    intro ht
    have h := first_not_mem_sq_of_span_triple_of_not_regular A t s z hgen hd hsing
    rw [ht] at h
    exact h (Ideal.zero_mem _)
  exact exists_original_cubic_of_normalized_kernel A hd hA hRat t s z ht hgen hker

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
