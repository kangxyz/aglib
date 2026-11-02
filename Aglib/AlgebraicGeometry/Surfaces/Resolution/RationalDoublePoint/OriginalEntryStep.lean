/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.PointLocalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoEntryCover

/-!
# First entry on an arbitrary original point blowup

The native point-localization square and the actual two-chart first-entry
producer retain the original scheme stalk, blowdown map, full entry identity,
parameter, coefficient, exceptional centre and structural residue map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalEntryStep

/-- First entry on the original scheme step, with the exact parameter and
coefficient alternatives from the two original charts of the same true cubic. -/
theorem marker_or_tripleEntry
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
    (F : CubicRelation t s z) (hn : F.coefficients.residueCubic ≠ 0)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y))
    (tC sC zC : maximalIdeal (B.Y.presheaf.stalk y))
    (hgenC : maximalIdeal (B.Y.presheaf.stalk y) = Ideal.span
      ({(tC : B.Y.presheaf.stalk y), (sC : B.Y.presheaf.stalk y),
        (zC : B.Y.presheaf.stalk y)} : Set (B.Y.presheaf.stalk y)))
    (hrankC : Module.finrank
      ((B.Y.presheaf.stalk y) ⧸ maximalIdeal (B.Y.presheaf.stalk y))
      (maximalIdeal (B.Y.presheaf.stalk y)).Cotangent = 3)
    (hkerC : doubleLineChildCotangentKernel (B.Y.presheaf.stalk y) ![sC, zC, tC] =
      Ideal.span {(MvPolynomial.X 1 :
        MvPolynomial (Fin 3) (ResidueField (B.Y.presheaf.stalk y))) ^ 2}) :
    let f := (Arc.pointLocalRingMap B.map y x hbase).hom
    (∃ r : maximalIdeal (X.presheaf.stalk x), ∃ M : MarkedCubic r, M.square = z) ∨
      (∃ p u w : maximalIdeal (B.Y.presheaf.stalk y), ∃ T : TripleEntryData p u w,
        (((p : B.Y.presheaf.stalk y) = f (t : X.presheaf.stalk x) ∧
            T.coefficient = f F.coefficients.a3) ∨
          ((p : B.Y.presheaf.stalk y) = f (s : X.presheaf.stalk x) ∧
            T.coefficient = f F.coefficients.a0)) ∧
        (p : B.Y.presheaf.stalk y) ∉ maximalIdeal (B.Y.presheaf.stalk y) ^ 2 ∧
        (maximalIdeal (X.presheaf.stalk x)).map f =
          Ideal.span {(p : B.Y.presheaf.stalk y)} ∧
        Function.Bijective (ResidueField.map f)) := by
  let A : Type u := X.presheaf.stalk x
  let C : Type u := B.Y.presheaf.stalk y
  let f : A →+* C := (Arc.pointLocalRingMap B.map y x hbase).hom
  let : IsLocalHom f := Arc.pointLocalRingMap_isLocal B.map y x hbase
  let D := Arc.pointBlowup A
  obtain ⟨_, _, yD, hyD, hDbase, _, ε, _, hε⟩ :=
    PointLocalization.exists_closed_point_stalkIso x hx B y hy hbase
  let S : Type u := D.Y.presheaf.stalk yD
  let c : A →+* S := D.map.stalkScalar yD
  let : IsLocalHom c := D.map.stalkScalar_isLocalHom_of_closedPoint yD hDbase
  let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
  have he : e.toRingHom.comp f = c := hε
  have hs : ¬ IsRegularLocalRing S := by
    intro h
    let : IsRegularLocalRing S := h
    exact hsing (IsRegularLocalRing.of_ringEquiv e.symm)
  let tS : maximalIdeal S := maximalIdealEquivMap (A := C) (B := S) e tC
  let sS : maximalIdeal S := maximalIdealEquivMap (A := C) (B := S) e sC
  let zS : maximalIdeal S := maximalIdealEquivMap (A := C) (B := S) e zC
  have hgenS : maximalIdeal S = Ideal.span ({(tS : S), (sS : S), (zS : S)} : Set S) :=
    maximalIdeal_span_triple_ringEquiv e tC sC zC hgenC
  have hfg : (maximalIdeal C).FG := by
    rw [hgenC]
    exact Submodule.fg_span (((Set.finite_singleton (zC : C)).insert (sC : C)).insert (tC : C))
  have hrankS :=
    (CaseTwoMarkedStalk.cotangent_finrank_ringEquiv (R := C) (S := S) e hfg).trans hrankC
  have hkerS : doubleLineChildCotangentKernel S ![sS, zS, tS] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (ResidueField S)) ^ 2} :=
    doubleLineChildCotangentKernel_square_ringEquiv e tC sC zC hkerC
  rcases CaseTwoEntryCover.marker_or_tripleEntry_at_closed_point
      D t s z hgen hker F hn yD hyD hDbase hs tS sS zS hgenS hrankS hkerS with
    hmarker | ⟨p0, u0, w0, T0, hcases, hmin, hcenter, hres⟩
  · exact Or.inl hmarker
  right
  obtain ⟨a, b, hp0, hcoef, hab⟩ : ∃ a b : A,
      (p0 : S) = c a ∧ T0.coefficient = c b ∧
      ((a = (t : A) ∧ b = F.coefficients.a3) ∨
        (a = (s : A) ∧ b = F.coefficients.a0)) := by
    rcases hcases with ⟨hp, hc⟩ | ⟨hp, hc⟩
    · exact ⟨t, F.coefficients.a3, hp, hc, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨s, F.coefficients.a0, hp, hc, Or.inr ⟨rfl, rfl⟩⟩
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm p0
  let u : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm u0
  let w : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm w0
  let T : TripleEntryData p u w := T0.map (A := S) (B := C) e.symm
  have hep : e.toRingHom (p : C) = c a := by
    change e (e.symm (p0 : S)) = c a
    exact (e.apply_symm_apply _).trans hp0
  have hminS : c a ∉ maximalIdeal S ^ 2 := by simpa only [hp0] using hmin
  have hcenterS : (maximalIdeal A).map c = Ideal.span {c a} := by
    simpa only [hp0] using hcenter
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he a (p : C) hep
  have htransport_min := htransport hminS
  have htransport_center := htransport_min hcenterS
  obtain ⟨hp, hmin', hcenter', hres'⟩ := htransport_center hres
  have hcoeff : T.coefficient = f b := by
    apply e.injective
    change e (e.symm T0.coefficient) = e (f b)
    rw [e.apply_symm_apply, hcoef]
    exact (RingHom.congr_fun he b).symm
  refine ⟨p, u, w, T, ?_, hmin', hcenter', hres'⟩
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨hp, hcoeff⟩
  · exact Or.inr ⟨hp, hcoeff⟩

end AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalEntryStep
