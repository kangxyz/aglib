/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoMarkedStalk
public import Aglib.RingTheory.LocalRing.ParameterEquiv

/-!
# Actual first entry on the original blowup stalk

The original point and full child kernel produce either a parent marker or
the entire first triple-entry identity on the original child scheme stalk.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoEntry

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))

/-- One actual Case-II child yields a genuine parent marker or full original-
stalk triple-entry data, retaining the original parameter and coefficient. -/
theorem marker_or_tripleEntry_at_closed_point
    (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2})
    (F : CubicRelation t s z) (hn : F.coefficients.residueCubic ≠ 0)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (hchart : x ∈ Set.range (CaseOneChart.chart B t))
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
    (∃ r : maximalIdeal A, ∃ M : MarkedCubic r, M.square = z) ∨
      (∃ p u w : maximalIdeal (B.Y.presheaf.stalk x),
        (p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) ∧
        ∃ T : TripleEntryData p u w,
          T.coefficient = B.map.stalkScalar x F.coefficients.a3 ∧
          (p : B.Y.presheaf.stalk x) ∉ maximalIdeal (B.Y.presheaf.stalk x) ^ 2 ∧
          (maximalIdeal A).map (B.map.stalkScalar x) =
            Ideal.span {(p : B.Y.presheaf.stalk x)} ∧
          Function.Bijective (ResidueField.map (B.map.stalkScalar x))) := by
  let C : Type u := B.Y.presheaf.stalk x
  let f : A →+* C := B.map.stalkScalar x
  let : IsLocalHom f := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
  let E := DoubleLinePresentation.ofKernel t s z hgen hker
  let D := E.reducedChart
  obtain ⟨P, hP, hdata⟩ := CaseTwoPoint.exists_actual_prime_parameter_at_closed_singular_point
    B t s z hgen hker F x hx hbase hsing hchart
  let : P.IsPrime := hP
  obtain ⟨q, Q, hm, hq, hPq, hQ, _, _, hd, hs, ε, hε⟩ := hdata
  let S := Localization.AtPrime P
  let c : A →+* S := localizedChartMap (maximalIdeal A) (t : A) P
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp f = c := hε
  have hg : maximalIdeal S = Ideal.span
      ({(D.primeTriple Q q hQ P hPq 2 : S), (D.primeTriple Q q hQ P hPq 0 : S),
        (D.primeTriple Q q hQ P hPq 1 : S)} : Set S) :=
    Ideal.localTriple_generates P
      (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)) Q
      (fractionElement (maximalIdeal A) t z) (D.prime_span Q q hQ P hPq)
  obtain ⟨L, hL, hkL⟩ := CaseTwoMarkedStalk.full_square_kernel_in_target_generators
    (R := C) (S := S) e tC sC zC hgenC hrankC hkerC (D.primeTriple Q q hQ P hPq) hg
  rcases entry_reduction D F hgen hker hn Q q hQ hq hm P hPq hd hs L hL hkL with
    hmarker | ⟨α, hP0, μ, T0, hcoef, hmin, hcenter, hlocal, hres⟩
  · exact Or.inl hmarker
  right
  let : IsLocalHom c := hlocal
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm
    ((D.recenter α).centeredTriple P hP0 2)
  let v : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm
    ((D.recenter α).centeredTriple P hP0 0)
  let w : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm
    ((D.recenter α).centeredTriple P hP0 1 + μ • (D.recenter α).centeredTriple P hP0 2)
  let T : TripleEntryData p v w := T0.map (A := S) (B := C) e.symm
  have hep : e.toRingHom (p : C) = c (t : A) := by
    change e (e.symm (c (t : A))) = c (t : A)
    exact e.apply_symm_apply _
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he (t : A) (p : C) hep
  have htransport_min := htransport hmin
  have htransport_center := htransport_min hcenter
  obtain ⟨hp, hmin', hcenter', hres'⟩ := htransport_center hres
  refine ⟨p, v, w, hp, T, ?_, hmin', hcenter', hres'⟩
  apply e.injective
  change e (e.symm T0.coefficient) = e (f F.coefficients.a3)
  rw [e.apply_symm_apply, hcoef]
  exact (RingHom.congr_fun he F.coefficients.a3).symm

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoEntry
