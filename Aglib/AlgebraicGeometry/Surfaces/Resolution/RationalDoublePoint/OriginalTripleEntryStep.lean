/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.PointLocalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoTripleEntry
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren

/-!
# Second entry on an arbitrary original point blowup

The same point-localization square transports the full second-entry marker.
Its ratio parameter is distinct from the image of the chart denominator,
which generates the original exceptional centre ideal.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away.SaturatedChart
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalTripleEntryStep

/-- Second entry on the original scheme step, retaining the ratio equation,
the denominator centre, full marker and original structural residue map. -/
theorem marker_or_next_marker
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdA : ringKrullDim (X.presheaf.stalk x) = 2)
    (hA : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hRat : NormalModificationH1Vanishing (X.presheaf.stalk x))
    (hsingA : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x)
    {t u w : maximalIdeal (X.presheaf.stalk x)} (T : TripleEntryData t u w)
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
    (∃ r : maximalIdeal (X.presheaf.stalk x), ∃ M : MarkedCubic r,
      M.other = t ∧ M.square = w) ∨
      (∃ r : maximalIdeal (B.Y.presheaf.stalk y), ∃ N : MarkedCubic r,
        f (t : X.presheaf.stalk x) = f (u : X.presheaf.stalk x) * r ∧
        (N.other : B.Y.presheaf.stalk y) = f (u : X.presheaf.stalk x) ∧
        f (w : X.presheaf.stalk x) = f (u : X.presheaf.stalk x) * N.square ∧
        IsLocalRing.residue (B.Y.presheaf.stalk y) N.relation.coefficients.a2 =
          IsLocalRing.residue (B.Y.presheaf.stalk y) (f T.coefficient) ∧
        (r : B.Y.presheaf.stalk y) ∉ maximalIdeal (B.Y.presheaf.stalk y) ^ 2 ∧
        (maximalIdeal (X.presheaf.stalk x)).map f =
          Ideal.span {f (u : X.presheaf.stalk x)} ∧
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
  rcases CaseTwoTripleEntry.marker_or_next_marker_at_closed_point
      D hdA hA hRat hsingA T yD hyD hDbase hs tS sS zS hgenS hrankS hkerS with
    hmarker | ⟨r0, N0, ht, hother, hw, hcoef, _, hcenter, hres⟩
  · exact Or.inl hmarker
  right
  have hproperties := singular_stalk_properties_of_rational_model A hA hdA hRat
    (MaximalIdealBlowup.map A hdA) (MaximalIdealBlowup.ordinary_normalStalks A hdA hA hRat)
    (MaximalIdealBlowup.map_fieldMap_isIso A hdA) yD hs
  let : IsNoetherianRing S := hproperties.2.2.1
  let : IsNoetherianRing C := isNoetherianRing_of_ringEquiv S (S := C) e.symm
  have hdS : ringKrullDim S = 2 := hproperties.2.2.2.2.1
  have hdC : ringKrullDim C = 2 :=
    (ringKrullDim_eq_of_ringEquiv (R := C) (S := S) e).trans hdS
  let r : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm r0
  let N : MarkedCubic r := N0.map (A := S) (B := C) e.symm
  have hg : maximalIdeal S = Ideal.span
      ({(N0.other : S), (r0 : S), (N0.square : S)} : Set S) := by
    simpa only [Set.insert_comm] using N0.generates
  have hminu : c (u : A) ∉ maximalIdeal S ^ 2 := by
    rw [← hother]
    exact first_not_mem_sq_of_span_triple_of_not_regular S
      N0.other r0 N0.square hg hdS hs
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he (u : A) (e.symm (c (u : A)))
      (e.apply_symm_apply _)
  have htransport_min := htransport hminu
  have htransport_center := htransport_min hcenter
  obtain ⟨huval, _, hcenter', hres'⟩ := htransport_center hres
  have heval (a : A) : e.symm.toRingHom (c a) = f a :=
    e.symm_apply_eq.mpr (RingHom.congr_fun he a).symm
  refine ⟨r, N, ?_, ?_, ?_, ?_, N.parameter_not_mem_sq hdC hsing, ?_, hres'⟩
  · have h := congrArg e.symm.toRingHom ht
    change e.symm.toRingHom (c (t : A)) = e.symm.toRingHom (c (u : A) * r0) at h
    rw [map_mul, heval, heval] at h
    exact h
  · change e.symm (N0.other : S) = f (u : A)
    rw [hother]
    exact huval
  · have h := congrArg e.symm.toRingHom hw
    change e.symm.toRingHom (c (w : A)) =
      e.symm.toRingHom (c (u : A) * N0.square) at h
    rw [map_mul, heval, heval] at h
    exact h
  · apply (ResidueField.mapEquiv (R := C) (S := S) e).injective
    change IsLocalRing.residue S (e (e.symm N0.relation.coefficients.a2)) =
      IsLocalRing.residue S (e (f T.coefficient))
    rw [e.apply_symm_apply]
    exact hcoef.trans (congrArg (IsLocalRing.residue S)
      (RingHom.congr_fun he T.coefficient).symm)
  · simpa only [huval] using hcenter'

end AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalTripleEntryStep
