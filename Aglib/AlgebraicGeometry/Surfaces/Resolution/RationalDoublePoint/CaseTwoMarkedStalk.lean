/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoPoints
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Successor
public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Equiv
public import Aglib.RingTheory.AssociatedGraded.Cotangent.Basis
public import Aglib.RingTheory.LocalRing.ParameterEquiv

/-!
# A genuine continuing Case-II marker on the original blowup stalk

Child rank, generators and full normalized kernel are supplied on the actual
scheme stalk. The original chart producer supplies its native localization
comparison. Native ideal generator rank and the full kernel transports then
derive the kernel on the literal primeTriple before invoking marked continuation.
The resulting full marker is returned on the original stalk, with the same
original parameter, coefficient and structural residue-field map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u v

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoMarkedStalk

private theorem span_range_of_three
    {R : Type u} [CommRing R] [IsLocalRing R] (g : Fin 3 → maximalIdeal R)
    (hgen : maximalIdeal R = Ideal.span ({(g 2 : R), (g 0 : R), (g 1 : R)} : Set R)) :
    Ideal.span (Set.range fun i => (g i : R)) = maximalIdeal R := by
  have hrange : Set.range (fun i => (g i : R)) = {(g 2 : R), (g 0 : R), (g 1 : R)} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hrange]
  exact hgen.symm

theorem cotangent_finrank_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (hfg : (maximalIdeal R).FG) :
    Module.finrank (S ⧸ maximalIdeal S) (maximalIdeal S).Cotangent =
      Module.finrank (R ⧸ maximalIdeal R) (maximalIdeal R).Cotangent := by
  have hm : (maximalIdeal R).map e.toRingHom = maximalIdeal S :=
    map_ringEquiv_maximalIdeal e
  have hfg' : (maximalIdeal S).FG := hm ▸ hfg.map e.toRingHom
  have hR := spanFinrank_eq_finrank_quotient (maximalIdeal R) hfg
  have hS := spanFinrank_eq_finrank_quotient (maximalIdeal S) hfg'
  have hr := Ideal.spanFinrank_map_eq_of_ringEquiv e (maximalIdeal R)
  rw [map_ringEquiv_maximalIdeal] at hr
  exact hS.symm.trans (hr.trans hR)

/-- Genuine original-stalk rank and full square kernel give the full square
kernel in any actual spanning target triple under the native ring equivalence. -/
theorem full_square_kernel_in_target_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (t s z : maximalIdeal R)
    (hgen : maximalIdeal R = Ideal.span ({(t : R), (s : R), (z : R)} : Set R))
    (hrank : Module.finrank (R ⧸ maximalIdeal R) (maximalIdeal R).Cotangent = 3)
    (hker : doubleLineChildCotangentKernel R ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField R)) ^ 2})
    (g : Fin 3 → maximalIdeal S)
    (hg : maximalIdeal S = Ideal.span ({(g 2 : S), (g 0 : S), (g 1 : S)} : Set S)) :
    ∃ L : MvPolynomial (Fin 3) (ResidueField S), L.IsHomogeneous 1 ∧
      doubleLineChildCotangentKernel S g = Ideal.span {L ^ 2} := by
  let g' : Fin 3 → maximalIdeal S :=
    ![maximalIdealEquivMap e s, maximalIdealEquivMap e z, maximalIdealEquivMap e t]
  have hgen' : maximalIdeal S =
      Ideal.span ({(g' 2 : S), (g' 0 : S), (g' 1 : S)} : Set S) :=
    maximalIdeal_span_triple_ringEquiv e t s z hgen
  have hfg : (maximalIdeal R).FG := by
    rw [hgen]
    exact Submodule.fg_span (((Set.finite_singleton (z : R)).insert (s : R)).insert (t : R))
  have hrank' := (cotangent_finrank_ringEquiv e hfg).trans hrank
  have hk' := doubleLineChildCotangentKernel_square_ringEquiv e t s z hker
  have hk : RingHom.ker (Ideal.cotangentPolynomialMap (maximalIdeal S) g').toRingHom =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (S ⧸ maximalIdeal S)) ^ 2} := by
    dsimp only [doubleLineChildCotangentKernel, ResidueField, ResidueField.field,
      Ideal.associatedGradedCommRing] at hk' ⊢
    exact hk'
  obtain ⟨L, hL, _, hkL⟩ := exists_cotangentBasisChange_square_kernel g' g
    (span_range_of_three g' hgen') (span_range_of_three g hg)
    (by simpa only [Fintype.card_fin] using hrank'.symm)
    (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X _ _)
    (MvPolynomial.X_ne_zero 1) hk
  refine ⟨L, ?_, ?_⟩
  · dsimp only [ResidueField, ResidueField.field] at hL ⊢
    exact hL
  · dsimp only [doubleLineChildCotangentKernel, ResidueField, ResidueField.field,
      Ideal.associatedGradedCommRing] at hkL ⊢
    exact hkL

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))

/-- A continuing actual Case-II child inherits a full corrected marker on its
original scheme stalk. Its prime, field maps and primeTriple kernel are derived;
only genuine child generators, rank and full normalized kernel are inputs. -/
theorem exists_marked_continuation_at_closed_point
    {t : maximalIdeal A} (M : MarkedCubic t)
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
    ∃ p : maximalIdeal (B.Y.presheaf.stalk x),
      (p : B.Y.presheaf.stalk x) = B.map.stalkScalar x (t : A) ∧
      ∃ N : MarkedCubic p,
        IsLocalRing.residue (B.Y.presheaf.stalk x) N.relation.coefficients.a2 =
          IsLocalRing.residue (B.Y.presheaf.stalk x)
            (B.map.stalkScalar x M.relation.coefficients.a2) ∧
        (p : B.Y.presheaf.stalk x) ∉ maximalIdeal (B.Y.presheaf.stalk x) ^ 2 ∧
        (maximalIdeal A).map (B.map.stalkScalar x) =
          Ideal.span {(p : B.Y.presheaf.stalk x)} ∧
        Function.Bijective (ResidueField.map (B.map.stalkScalar x)) := by
  let C : Type u := B.Y.presheaf.stalk x
  let f : A →+* C := B.map.stalkScalar x
  let : IsLocalHom f := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
  let E := DoubleLinePresentation.ofKernel t M.other M.square M.generates M.tangent
  let D := E.reducedChart
  obtain ⟨P, hP, hdata⟩ := CaseTwoPoint.exists_actual_prime_parameter_at_closed_singular_point
    B t M.other M.square M.generates M.tangent M.relation x hx hbase hsing hchart
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
      (fractionElement (maximalIdeal A) t M.square) (D.prime_span Q q hQ P hPq)
  obtain ⟨L, hL, hkL⟩ := full_square_kernel_in_target_generators (R := C) (S := S) e tC sC zC
    hgenC hrankC hkerC (D.primeTriple Q q hQ P hPq) hg
  obtain ⟨α, μ, N0, _, _, hcoef, hmin, hcenter, hlocal, hres⟩ :=
    marked_continuation M D Q q hQ hq hm P hPq hd hs L hL hkL
  let : IsLocalHom c := hlocal
  let p : maximalIdeal C :=
    maximalIdealEquivMap (A := S) (B := C) e.symm (D.primeTriple Q q hQ P hPq 2)
  let N : MarkedCubic p := N0.map (A := S) (B := C) e.symm
  have hep : e.toRingHom (p : C) = c (t : A) := by
    change e (e.symm (c (t : A))) = c (t : A)
    exact e.apply_symm_apply _
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he (t : A) (p : C) hep
  have htransport_min := htransport hmin
  have htransport_center := htransport_min hcenter
  obtain ⟨hp, hmin', hcenter', hres'⟩ := htransport_center hres
  refine ⟨p, hp, N, ?_, hmin', hcenter', hres'⟩
  · apply (ResidueField.mapEquiv (R := C) (S := S) e).injective
    change IsLocalRing.residue S (e (e.symm N0.relation.coefficients.a2)) =
      IsLocalRing.residue S (e (f M.relation.coefficients.a2))
    rw [e.apply_symm_apply]
    exact hcoef.trans (congrArg (IsLocalRing.residue S)
      (RingHom.congr_fun he M.relation.coefficients.a2).symm)

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseTwoMarkedStalk
