/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoMarkedStalk

/-!
# Actual marker-chart coverage of continuing Case-II children

The original swapped cubic excludes the missing point of the opposite chart.
The same native affine-atlas overlap then puts every continuing child in the
marker chart, without assuming an overlap or a transported marker.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoMarkedCover

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))

/-- The actual continuing child belongs to the original marker chart, even
when it was first found in the opposite chart of the same native atlas. -/
theorem mem_parameterChart_of_closed_caseTwo_point
    {t : maximalIdeal A} (M : MarkedCubic t)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (tC sC zC : maximalIdeal (B.Y.presheaf.stalk x))
    (hgenC : maximalIdeal (B.Y.presheaf.stalk x) = Ideal.span
      ({(tC : B.Y.presheaf.stalk x), (sC : B.Y.presheaf.stalk x),
        (zC : B.Y.presheaf.stalk x)} : Set (B.Y.presheaf.stalk x)))
    (hrankC : Module.finrank
      ((B.Y.presheaf.stalk x) ⧸ maximalIdeal (B.Y.presheaf.stalk x))
      (maximalIdeal (B.Y.presheaf.stalk x)).Cotangent = 3)
    (hkerC : doubleLineChildCotangentKernel (B.Y.presheaf.stalk x) ![sC, zC, tC] =
      Ideal.span {(MvPolynomial.X 1 :
        MvPolynomial (Fin 3) (ResidueField (B.Y.presheaf.stalk x))) ^ 2}) :
    x ∈ Set.range (CaseOneChart.chart B t) := by
  obtain hmarker | hother := CaseTwoPoint.mem_planeChart_or_opposite_of_closed_exceptional_point
    B t M.other M.square M.generates M.tangent x hx hbase
  · exact hmarker
  have hg : maximalIdeal A = Ideal.span ({(M.other : A), (t : A), (M.square : A)} : Set A) := by
    simpa only [Set.insert_comm] using M.generates
  have hk : doubleLineChildCotangentKernel A ![t, M.square, M.other] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
    have h := cotangentKernel_planeChange ![M.other, M.square, t] 0 1 1 0 (by simp) M.tangent
    simpa only [planeChangeTriple_triple, zero_smul, one_smul, zero_add, add_zero] using h
  let E := DoubleLinePresentation.ofKernel M.other t M.square hg hk
  let D := E.reducedChart
  obtain ⟨P, hP, hdata⟩ := CaseTwoPoint.exists_actual_prime_parameter_at_closed_singular_point
    B M.other t M.square hg hk M.relation.swap x hx hbase hsing hother
  let : P.IsPrime := hP
  obtain ⟨q, Q, hm, hq, hPq, hQ, _, hpoint, hd, hs, ε, _⟩ := hdata
  let C : Type u := B.Y.presheaf.stalk x
  let S := Localization.AtPrime P
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  have hgP : maximalIdeal S = Ideal.span
      ({(D.primeTriple Q q hQ P hPq 2 : S), (D.primeTriple Q q hQ P hPq 0 : S),
        (D.primeTriple Q q hQ P hPq 1 : S)} : Set S) :=
    Ideal.localTriple_generates P
      (algebraMap A (saturatedChart A (maximalIdeal A) (M.other : A)) (M.other : A)) Q
      (fractionElement (maximalIdeal A) M.other M.square) (D.prime_span Q q hQ P hPq)
  obtain ⟨L, hL, hkL⟩ := CaseTwoMarkedStalk.full_square_kernel_in_target_generators
    (R := C) (S := S) e tC sC zC hgenC hrankC hkerC (D.primeTriple Q q hQ P hPq) hgP
  have hnot := marked_opposite_parameter_not_mem M D Q q hQ hq hm P hPq hd hs L hL hkL
  have hloc : (⟨P, hP⟩ : PrimeSpectrum (saturatedChart A (maximalIdeal A) (M.other : A))) ∈
      Set.range (affineOverlapMap A (maximalIdeal A) M.other t) := by
    change (⟨P, hP⟩ : PrimeSpectrum (affineBlowupAlgebra A (maximalIdeal A) M.other)) ∈
      Set.range (PrimeSpectrum.comap
        (algebraMap (affineBlowupAlgebra A (maximalIdeal A) M.other)
          (Localization.Away (ratio A (maximalIdeal A) M.other t))))
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (ratio A (maximalIdeal A) M.other t))
      (ratio A (maximalIdeal A) M.other t)]
    exact hnot
  obtain ⟨w, hw⟩ := hloc
  have hr : x ∈ Set.range
      (affineOverlapMap A (maximalIdeal A) M.other t ≫ (affineAtlas B).chart M.other) := by
    refine ⟨w, ?_⟩
    change CaseOneChart.chart B M.other
      (affineOverlapMap A (maximalIdeal A) M.other t w) = x
    rw [hw]
    exact hpoint
  rw [(affineAtlas B).overlap] at hr
  exact hr.2

/-- Every actual continuing Case-II child carries the same original marker
parameter on its original stalk. No preferred-chart or overlap premise remains. -/
theorem exists_marked_continuation_at_closed_point
    {t : maximalIdeal A} (M : MarkedCubic t)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (tC sC zC : maximalIdeal (B.Y.presheaf.stalk x))
    (hgenC : maximalIdeal (B.Y.presheaf.stalk x) = Ideal.span
      ({(tC : B.Y.presheaf.stalk x), (sC : B.Y.presheaf.stalk x),
        (zC : B.Y.presheaf.stalk x)} : Set (B.Y.presheaf.stalk x)))
    (hrankC : Module.finrank
      ((B.Y.presheaf.stalk x) ⧸ maximalIdeal (B.Y.presheaf.stalk x))
      (maximalIdeal (B.Y.presheaf.stalk x)).Cotangent = 3)
    (hkerC : doubleLineChildCotangentKernel (B.Y.presheaf.stalk x) ![sC, zC, tC] =
      Ideal.span {(MvPolynomial.X 1 :
        MvPolynomial (Fin 3) (ResidueField (B.Y.presheaf.stalk x))) ^ 2}) :
    letI := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
    ∃ p : maximalIdeal (B.Y.presheaf.stalk x),
      (p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) ∧
      ∃ N : MarkedCubic p,
        IsLocalRing.residue (B.Y.presheaf.stalk x) N.relation.coefficients.a2 =
          IsLocalRing.residue (B.Y.presheaf.stalk x)
            (B.map.stalkScalar x M.relation.coefficients.a2) ∧
        (p : B.Y.presheaf.stalk x) ∉ maximalIdeal (B.Y.presheaf.stalk x) ^ 2 ∧
        (maximalIdeal A).map (B.map.stalkScalar x) =
          Ideal.span {(p : B.Y.presheaf.stalk x)} ∧
        Function.Bijective (ResidueField.map (B.map.stalkScalar x)) :=
  CaseTwoMarkedStalk.exists_marked_continuation_at_closed_point B M x hx hbase hsing
    (mem_parameterChart_of_closed_caseTwo_point B M x hx hbase hsing tC sC zC hgenC hrankC hkerC)
    tC sC zC hgenC hrankC hkerC

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoMarkedCover
