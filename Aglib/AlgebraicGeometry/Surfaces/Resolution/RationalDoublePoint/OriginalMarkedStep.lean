/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.PointLocalization
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoMarkedCover

/-!
# Marked continuation on an arbitrary original point blowup

The point-localization comparison retains the original scheme, blowup datum,
selected points and pointLocalRingMap. Actual normalized child data is given
on the original scheme stalk; its local-blowup rank and whole kernel are
transported, not supplied. The full marker returns through the same native
stalk equivalence with the original parameter, centre and residue map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalMarkedStep

/-- A continuing Case-II point of an arbitrary original point blowup inherits
the same original marker through the original blowdown point-local-ring map. -/
theorem exists_marked_continuation
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x)
    {t : maximalIdeal (X.presheaf.stalk x)} (M : MarkedCubic t)
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
    ∃ p : maximalIdeal (B.Y.presheaf.stalk y),
      (p : B.Y.presheaf.stalk y) = f (t : X.presheaf.stalk x) ∧
      ∃ N : MarkedCubic p,
        IsLocalRing.residue (B.Y.presheaf.stalk y) N.relation.coefficients.a2 =
          IsLocalRing.residue (B.Y.presheaf.stalk y) (f M.relation.coefficients.a2) ∧
        (p : B.Y.presheaf.stalk y) ∉ maximalIdeal (B.Y.presheaf.stalk y) ^ 2 ∧
        (maximalIdeal (X.presheaf.stalk x)).map f =
          Ideal.span {(p : B.Y.presheaf.stalk y)} ∧
        Function.Bijective (ResidueField.map f) := by
  let A : Type u := X.presheaf.stalk x
  let C : Type u := B.Y.presheaf.stalk y
  let f : A →+* C := (Arc.pointLocalRingMap B.map y x hbase).hom
  let : IsLocalHom f := Arc.pointLocalRingMap_isLocal B.map y x hbase
  let D := Arc.pointBlowup A
  obtain ⟨_, _, z, hz, hzbase, hcy, ε, _, hε⟩ :=
    PointLocalization.exists_closed_point_stalkIso x hx B y hy hbase
  let S : Type u := D.Y.presheaf.stalk z
  let c : A →+* S := D.map.stalkScalar z
  let : IsLocalHom c := D.map.stalkScalar_isLocalHom_of_closedPoint z hzbase
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
  obtain ⟨p0, hp0, N0, hcoef, hmin, hcenter, hres⟩ :=
    CaseTwoMarkedCover.exists_marked_continuation_at_closed_point
      D M z hz hzbase hs tS sS zS hgenS hrankS hkerS
  let p : maximalIdeal C := maximalIdealEquivMap (A := S) (B := C) e.symm p0
  let N : MarkedCubic p := N0.map (A := S) (B := C) e.symm
  have hep : e.toRingHom (p : C) = c (t : A) := by
    change e (e.symm (p0 : S)) = c (t : A)
    exact (e.apply_symm_apply _).trans hp0
  have hminS : c (t : A) ∉ maximalIdeal S ^ 2 := by
    simpa only [hp0] using hmin
  have hcenterS : (maximalIdeal A).map c = Ideal.span {c (t : A)} := by
    simpa only [hp0] using hcenter
  have htransport := parameter_properties_of_equiv_comp
    (A := A) (R := C) (S := S) f c e he (t : A) (p : C) hep
  have htransport_min := htransport hminS
  have htransport_center := htransport_min hcenterS
  obtain ⟨hp, hmin', hcenter', hres'⟩ := htransport_center hres
  refine ⟨p, hp, N, ?_, hmin', hcenter', hres'⟩
  apply (ResidueField.mapEquiv (R := C) (S := S) e).injective
  change IsLocalRing.residue S (e (e.symm N0.relation.coefficients.a2)) =
    IsLocalRing.residue S (e (f M.relation.coefficients.a2))
  rw [e.apply_symm_apply]
  exact hcoef.trans (congrArg (IsLocalRing.residue S)
    (RingHom.congr_fun he M.relation.coefficients.a2).symm)

end AlgebraicGeometry.Scheme.RationalDoublePoint.OriginalMarkedStep
