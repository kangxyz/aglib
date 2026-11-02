/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoPoints
public import Aglib.AlgebraicGeometry.Blowup.PointLocalization
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Equiv
public import Aglib.RingTheory.RegularLocalRing.ThreeGenerators

/-!
# Genuine Case-II child generators before the child cone

The original prime parameter and actual two-chart cover give three generators
on every original closed singular child stalk. Dimension and nonregularity
then give cotangent rank three, without a child Hilbert or kernel premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoChildGenerators

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]

private theorem exists_generators_of_parameterChart
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))
    (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2})
    (F : CubicRelation t s z)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (hchart : x ∈ Set.range (CaseOneChart.chart B t)) :
    ringKrullDim (B.Y.presheaf.stalk x) = 2 ∧
      ∃ p u v : maximalIdeal (B.Y.presheaf.stalk x),
        maximalIdeal (B.Y.presheaf.stalk x) = Ideal.span
          ({(p : B.Y.presheaf.stalk x), (u : B.Y.presheaf.stalk x),
            (v : B.Y.presheaf.stalk x)} : Set (B.Y.presheaf.stalk x)) ∧
        Module.finrank (ResidueField (B.Y.presheaf.stalk x))
          (CotangentSpace (B.Y.presheaf.stalk x)) = 3 ∧
        (p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) := by
  let C : Type u := B.Y.presheaf.stalk x
  let D := (DoubleLinePresentation.ofKernel t s z hgen hker).reducedChart
  obtain ⟨P, hP, hdata⟩ := CaseTwoPoint.exists_actual_prime_parameter_at_closed_singular_point
    B t s z hgen hker F x hx hbase hsing hchart
  let : P.IsPrime := hP
  obtain ⟨q, Q, _, _, hPq, hQ, _, _, hd, _, ε, hε⟩ := hdata
  let S := Localization.AtPrime P
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  let f : A →+* C := B.map.stalkScalar x
  let c : A →+* S := localizedChartMap (maximalIdeal A) (t : A) P
  have he : e.toRingHom.comp f = c := hε
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing P.primeCompl S
    (saturatedChart_isNoetherian (maximalIdeal A) (t : A))
  let : IsNoetherianRing C := isNoetherianRing_of_ringEquiv S (S := C) e.symm
  let pS := D.primeTriple Q q hQ P hPq 2
  let uS := D.primeTriple Q q hQ P hPq 0
  let vS := D.primeTriple Q q hQ P hPq 1
  have hgenS : maximalIdeal S = Ideal.span ({(pS : S), (uS : S), (vS : S)} : Set S) :=
    Ideal.localTriple_generates P
      (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)) Q
      (fractionElement (maximalIdeal A) t z) (D.prime_span Q q hQ P hPq)
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm pS
  let u : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm uS
  let v : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm vS
  have hgenLaw := maximalIdeal_span_triple_ringEquiv (A := S) (B := C) e.symm pS uS vS
  have hgenNative := hgenLaw hgenS
  have hgenC : maximalIdeal C = Ideal.span ({(p : C), (u : C), (v : C)} : Set C) := by
    exact hgenNative
  have hdC : ringKrullDim C = 2 :=
    (ringKrullDim_eq_of_ringEquiv (R := C) (S := S) e).trans hd
  refine ⟨hdC, p, u, v, hgenC, ?_, ?_⟩
  · exact cotangent_finrank_eq_three_of_maximalIdeal_span_triple hdC hsing p u v hgenC
  · apply e.injective
    change e (e.symm (c (t : A))) = e (f (t : A))
    rw [e.apply_symm_apply]
    exact (RingHom.congr_fun he (t : A)).symm

/-- The actual two charts give original child generators and cotangent rank
before any child Hilbert/kernel input. The denominator records its real chart. -/
theorem exists_generators_at_closed_singular_point
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))
    (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2})
    (F : CubicRelation t s z)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x)) :
    ringKrullDim (B.Y.presheaf.stalk x) = 2 ∧
      ∃ p u v : maximalIdeal (B.Y.presheaf.stalk x),
        maximalIdeal (B.Y.presheaf.stalk x) = Ideal.span
          ({(p : B.Y.presheaf.stalk x), (u : B.Y.presheaf.stalk x),
            (v : B.Y.presheaf.stalk x)} : Set (B.Y.presheaf.stalk x)) ∧
        Module.finrank (ResidueField (B.Y.presheaf.stalk x))
          (CotangentSpace (B.Y.presheaf.stalk x)) = 3 ∧
        ((p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) ∨
          (p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (s : A)) := by
  obtain ht | hs := CaseTwoPoint.mem_planeChart_or_opposite_of_closed_exceptional_point
    B t s z hgen hker x hx hbase
  · obtain ⟨hd, p, u, v, hg, hr, hp⟩ := exists_generators_of_parameterChart
      B t s z hgen hker F x hx hbase hsing ht
    exact ⟨hd, p, u, v, hg, hr, Or.inl hp⟩
  · have hgen' : maximalIdeal A = Ideal.span ({(s : A), (t : A), (z : A)} : Set A) := by
      simpa only [Set.insert_comm] using hgen
    have hker' : doubleLineChildCotangentKernel A ![t, z, s] =
        Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField A)) ^ 2} := by
      have h := cotangentKernel_planeChange ![s, z, t] 0 1 1 0 (by simp) hker
      simpa only [planeChangeTriple_triple, zero_smul, one_smul, zero_add, add_zero] using h
    obtain ⟨hd, p, u, v, hg, hr, hp⟩ := exists_generators_of_parameterChart
      B s t z hgen' hker' F.swap x hx hbase hsing hs
    exact ⟨hd, p, u, v, hg, hr, Or.inr hp⟩

/-- The same child-generation result on an arbitrary original scheme step,
with the literal original point-local-ring homomorphism. -/
theorem exists_original_generators
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x)
    (t s z : maximalIdeal (X.presheaf.stalk x))
    (hgen : maximalIdeal (X.presheaf.stalk x) = Ideal.span
      ({(t : X.presheaf.stalk x), (s : X.presheaf.stalk x), (z : X.presheaf.stalk x)} :
        Set (X.presheaf.stalk x)))
    (hker : doubleLineChildCotangentKernel (X.presheaf.stalk x) ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 :
        MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x))) ^ 2})
    (F : CubicRelation t s z) (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)) :
    let f := (Arc.pointLocalRingMap B.map y x hbase).hom
    ringKrullDim (B.Y.presheaf.stalk y) = 2 ∧
      ∃ p u v : maximalIdeal (B.Y.presheaf.stalk y),
        maximalIdeal (B.Y.presheaf.stalk y) = Ideal.span
          ({(p : B.Y.presheaf.stalk y), (u : B.Y.presheaf.stalk y),
            (v : B.Y.presheaf.stalk y)} : Set (B.Y.presheaf.stalk y)) ∧
        Module.finrank (ResidueField (B.Y.presheaf.stalk y))
          (CotangentSpace (B.Y.presheaf.stalk y)) = 3 ∧
        ((p : B.Y.presheaf.stalk y) = f (t : X.presheaf.stalk x) ∨
          (p : B.Y.presheaf.stalk y) = f (s : X.presheaf.stalk x)) := by
  let A : Type u := X.presheaf.stalk x
  let C : Type u := B.Y.presheaf.stalk y
  let f : A →+* C := (Arc.pointLocalRingMap B.map y x hbase).hom
  let D := Arc.pointBlowup A
  obtain ⟨_, _, yD, hyD, hDbase, _, ε, _, hε⟩ :=
    PointLocalization.exists_closed_point_stalkIso x hx B y hy hbase
  let S : Type u := D.Y.presheaf.stalk yD
  let c : A →+* S := D.map.stalkScalar yD
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp f = c := hε
  have hs : ¬ IsRegularLocalRing S := by
    intro h
    let : IsRegularLocalRing S := h
    exact hsing (IsRegularLocalRing.of_ringEquiv e.symm)
  obtain ⟨hdS, pS, uS, vS, hgS, _, hpS⟩ :=
    exists_generators_at_closed_singular_point D t s z hgen hker F yD hyD hDbase hs
  let : IsProper D.map := D.isProper_of_spectrum
  let : IsLocallyNoetherian D.Y := LocallyOfFiniteType.isLocallyNoetherian D.map
  let : IsNoetherianRing S := inferInstance
  let : IsNoetherianRing C := isNoetherianRing_of_ringEquiv S (S := C) e.symm
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm pS
  let u : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm uS
  let v : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm vS
  have hgC : maximalIdeal C = Ideal.span ({(p : C), (u : C), (v : C)} : Set C) :=
    maximalIdeal_span_triple_ringEquiv e.symm pS uS vS hgS
  have hdC : ringKrullDim C = 2 :=
    (ringKrullDim_eq_of_ringEquiv (R := C) (S := S) e).trans hdS
  have hp (a : A) (ha : (pS : S) = c a) : (p : C) = f a := by
    apply e.injective
    change e (e.symm (pS : S)) = e (f a)
    rw [e.apply_symm_apply, ha]
    exact (RingHom.congr_fun he a).symm
  refine ⟨hdC, p, u, v, hgC,
    cotangent_finrank_eq_three_of_maximalIdeal_span_triple hdC hsing p u v hgC, ?_⟩
  exact hpS.elim (fun h => Or.inl (hp t h)) (fun h => Or.inr (hp s h))

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoChildGenerators
