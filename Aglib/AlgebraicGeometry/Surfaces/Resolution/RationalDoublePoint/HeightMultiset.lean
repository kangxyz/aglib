/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Height.Multiset
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FinitePrefixGeometry
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.PointHeight
public import Mathlib.Data.Multiset.DershowitzManna

/-!
# Strict decrease of the actual singular-height multiset

The actual centre is replaced by its finitely many strictly smaller singular
children; every other original singular point has its unique unchanged-height
lift through the native complement isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

/-- The existing native height multiset strictly decreases under the actual
blowup at a singular point. Finiteness on the new source is derived, not supplied. -/
theorem exists_pointBlowup_heightMultiset_lt
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsNagataRing.{u, 0} R) (hdR : ringKrullDim R = 2)
    (hRat : NormalModificationH1Vanishing R)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hfinX : {z : X | ¬ IsRegularLocalRing (X.presheaf.stalk z)}.Finite)
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (hlevels : ∀ z : X, ¬ IsRegularLocalRing (X.presheaf.stalk z) →
      ∃ n, IsEmpty (SingularPrefix X z n)) :
    let B := blowupDatum (X.fromSpecResidueField x).ker
    ∃ hfinB : {y : B.Y | ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)}.Finite,
      ∃ hnew : ∀ y : B.Y, ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) →
          ∃ n, IsEmpty (SingularPrefix B.Y y n),
        Multiset.IsDershowitzMannaLT
          (heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := B.Y) hfinB hnew) (heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := X) hfinX hlevels) := by
  classical
  let B := blowupDatum (X.fromSpecResidueField x).ker
  obtain ⟨_, _, _, _, _, hclosed, _, _, _, _⟩ :=
    singular_stalk_properties_of_rational_model R hR hdR hRat f hX hff x hx
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  have hfinB : {y : B.Y | ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)}.Finite :=
    finite_singularSet_datum_of_rational_model R hR hdR hRat f hff hX x hx (n := 0)
      (PUnit.unit : SingularPrefix X x 0)
  obtain ⟨hnew, hcentre, haway⟩ :=
    pointBlowup_singularHeight_step R hR hdR hRat f hX hff x hx hlevels
  refine ⟨hfinB, hnew, ?_⟩
  let S := hfinX.toFinset
  let T := hfinB.toFinset
  let SA := T.filter fun y => B.map y ≠ x
  let SF := T.filter fun y => B.map y = x
  let O := S.erase x
  let wX := fun z : X => if hz : ¬ IsRegularLocalRing (X.presheaf.stalk z) then
    height (hlevels z hz) else 0
  let wY := fun y : B.Y => if hy : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) then
    height (hnew y hy) else 0
  have hmeasureX : heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := X) hfinX hlevels = S.val.map wX :=
    heightMultiset_eq_map
      (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
      (X := X) hfinX hlevels wX (fun z hz => by simp only [wX, dite_eq_left hz])
  have hmeasureY : heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := B.Y) hfinB hnew = T.val.map wY :=
    heightMultiset_eq_map
      (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
      (X := B.Y) hfinB hnew wY (fun y hy => by simp only [wY, dite_eq_left hy])
  have hxS : x ∈ S := hfinX.mem_toFinset.mpr hx
  have himage : SA.image B.map = O := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hyT, hyx⟩ := Finset.mem_filter.mp hy
      have hySing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) :=
        hfinB.mem_toFinset.mp hyT
      obtain ⟨hzSing, _⟩ := haway y hySing hyx
      exact Finset.mem_erase.mpr ⟨hyx, hfinX.mem_toFinset.mpr hzSing⟩
    · intro hz
      obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hz
      have hzSing : ¬ IsRegularLocalRing (X.presheaf.stalk z) :=
        hfinX.mem_toFinset.mp hzS
      have hzCentre : z ∉ ((X.fromSpecResidueField x).ker.support : Set X) := by
        rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hclosed.closure_eq]
        exact hzx
      obtain ⟨y, hyp⟩ := B.mem_range_of_not_mem_support hzCentre
      have hyx : B.map y ≠ x := by rwa [hyp]
      have hySing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) := by
        intro hyreg
        let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hclosed y hyx
        let : IsRegularLocalRing (B.Y.presheaf.stalk y) := hyreg
        have hr : IsRegularLocalRing (X.presheaf.stalk (B.map y)) :=
          IsRegularLocalRing.of_ringEquiv
            (asIso (B.map.stalkMap y)).symm.commRingCatIsoToRingEquiv
        exact hzSing (Eq.mp (congrArg
          (fun z : X => IsRegularLocalRing (X.presheaf.stalk z)) hyp) hr)
      exact Finset.mem_image.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hfinB.mem_toFinset.mpr hySing, hyx⟩, hyp⟩
  have hinj : Set.InjOn B.map (SA : Set B.Y) :=
    (pointBlowup_injOn_complement x hclosed).mono fun y hy => (Finset.mem_filter.mp hy).2
  have himageVal : O.val = SA.val.map B.map :=
    (congrArg Finset.val himage).symm.trans (Finset.image_val_of_injOn hinj)
  have houtside : SA.val.map wY = O.val.map wX := by
    rw [himageVal, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro y hy
    obtain ⟨hyT, hyx⟩ := Finset.mem_filter.mp hy
    have hySing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) :=
      hfinB.mem_toFinset.mp hyT
    obtain ⟨hzSing, he⟩ := haway y hySing hyx
    have hz : ¬ IsRegularLocalRing (X.presheaf.stalk (B.map y)) := hzSing
    change wY y = wX (B.map y)
    calc
      wY y = height (hnew y hySing) := dite_eq_left hySing
      _ = height (hlevels (B.map y) hz) := he
      _ = wX (B.map y) := by
        have hw : wX (B.map y) = height (hlevels (B.map y) hz) := dite_eq_left hz
        exact hw.symm
  let common := O.val.map wX
  let children := SF.val.map wY
  have hpartition : SA.val + SF.val = T.val := by
    simpa only [SA, SF, Finset.filter_val, not_not] using
      Multiset.filter_add_not (p := fun y : B.Y => B.map y ≠ x) T.val
  have hnewMeasure : heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := B.Y) hfinB hnew = common + children := by
    rw [hmeasureY]
    calc
      _ = (SA.val + SF.val).map wY := congrArg (Multiset.map wY) hpartition.symm
      _ = SA.val.map wY + SF.val.map wY := Multiset.map_add _ _ _
      _ = common + children := congrArg (fun m : Multiset ℕ => m + children) houtside
  have holdMeasure : heightMultiset
            (eligible := fun Y y => ¬ IsRegularLocalRing (Y.presheaf.stalk y))
            (X := X) hfinX hlevels = common + {wX x} := by
    rw [hmeasureX]
    calc
      _ = (x ::ₘ S.val.erase x).map wX :=
        congrArg (Multiset.map wX) (Multiset.cons_erase hxS).symm
      _ = {wX x} + O.val.map wX := by
        simp only [O, Finset.erase_val, Multiset.map_cons, Multiset.singleton_add]
      _ = common + {wX x} := add_comm _ _
  refine ⟨common, children, {wX x}, by simp, hnewMeasure, holdMeasure, ?_⟩
  intro n hn
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hn
  obtain ⟨hyT, hyx⟩ := Finset.mem_filter.mp hy
  have hySing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) :=
    hfinB.mem_toFinset.mp hyT
  refine ⟨wX x, by simp, ?_⟩
  simpa only [wX, wY, dite_eq_left hx, dite_eq_left hySing] using hcentre y hySing hyx

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
