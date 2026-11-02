/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.ModelLocalization
public import Aglib.AlgebraicGeometry.FunctionField.LocalSpectrum.BaseChange
public import Aglib.AlgebraicGeometry.Surfaces.Birational.StalkNagata
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RingEquiv
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Gorenstein.RationalPropagation

/-!
# Rationality at original supported model stalks

Localize the actual proper birational model at ONE original rational target
stalk. A closed nongeneric source point above it has a closed nongeneric
lift to the literal pullback. Genuine local rationality propagation and
Nagata of its actual stalk transfer through the original stalk-arrow iso.
No global target rationality, normality or Noetherianity is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- A closed nongeneric original stalk above a rational Nagata local surface
point is itself Nagata and universally H1-vanishing. Only the original target
stalk is assumed rational, and its dimension is genuinely two. -/
theorem stalk_isNagata_and_normalModificationH1Vanishing_of_target_stalk
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (x : X) (hS : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hdS : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : NormalModificationH1Vanishing (X.presheaf.stalk x))
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyη : y ≠ genericPoint Y)
    (hgy : g y = x) :
    IsNagataRing.{u, 0} (Y.presheaf.stalk y) ∧
      NormalModificationH1Vanishing (Y.presheaf.stalk y) := by
  let S := X.presheaf.stalk x
  let : IsNoetherianRing S := hS.isNoetherianRing
  let s := X.fromSpecStalk x
  let P := pullback g s
  let a : P ⟶ Y := pullback.fst g s
  let p : P ⟶ Spec S := pullback.snd g s
  have H : IsPullback a p g s := IsPullback.of_hasPullback g s
  let : Flat s := fromSpecStalk_flat X x
  let : IsIntegral P := isIntegral_pullback_fromSpecStalk g x
  let : IsDominant a := isDominant_pullback_fst_fromSpecStalk g x
  let : Surjective g :=
    surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  let : Surjective p := inferInstance
  let : IsDominant p := inferInstance
  let : IsProper p := inferInstance
  have hpff : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    functionFieldMap_isIso_of_isPullback_fromSpecStalk g x a p H hff
  have hP : NormalStalks P := normalStalks_pullback_fromSpecStalk g x hY
  obtain ⟨t, hat, _, ht⟩ := exists_closed_point_pullback_fromSpecStalk g y x hgy hy
  have htη : t ≠ genericPoint P := by
    intro he
    apply hyη
    calc
      y = a t := hat.symm
      _ = a (genericPoint P) := congrArg a he
      _ = genericPoint Y := Scheme.map_genericPoint_of_isDominant P a
  let E : Arrow.mk (g.stalkMap y) ≅ Arrow.mk (p.stalkMap t) :=
    Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion H t y hat
  let e : (Y.presheaf.stalk y) ≃+* (P.presheaf.stalk t) :=
    (Arrow.rightFunc.mapIso E).commRingCatIsoToRingEquiv
  have hNP : IsNagataRing.{u, 0} (P.presheaf.stalk t) :=
    Scheme.stalk_isNagataRing_of_birational_surface S hS hdS.le p hpff t
  have hNY : IsNagataRing.{u, 0} (Y.presheaf.stalk y) := by
    let : Algebra (P.presheaf.stalk t) (Y.presheaf.stalk y) := e.symm.toRingHom.toAlgebra
    let : Module.Finite (P.presheaf.stalk t) (Y.presheaf.stalk y) :=
      RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective
    exact hNP.of_finite
  have hRatP : NormalModificationH1Vanishing (P.presheaf.stalk t) :=
    normalModificationH1Vanishing_stalk_of_normalModificationH1Vanishing
      S hS hdS hRat p hP hpff t ht htη
  exact ⟨hNY, (normalModificationH1Vanishing_iff_of_ringEquiv e).mpr hRatP⟩

end AlgebraicGeometry.Scheme.RationalSingularities
