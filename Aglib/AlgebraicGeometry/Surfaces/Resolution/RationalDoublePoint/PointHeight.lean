/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Height.BaseChange
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.PointNormality

/-!
# Actual singular height under the original point blowup

Existing finite empty-level witnesses are inherited by the actual next source.
Their least levels decrease over the centre and are unchanged away from it,
through two original open maps from the same complement pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

private theorem empty_level_and_height_pointBlowup_away
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x)
    (hclosed : IsClosed ({y} : Set (blowupDatum (X.fromSpecResidueField x).ker).Y))
    (himage : IsClosed ({(blowupDatum (X.fromSpecResidueField x).ker).map y} : Set X))
    (hold : ∃ n, IsEmpty (SingularPrefix X
      ((blowupDatum (X.fromSpecResidueField x).ker).map y) n)) :
    ∃ hnew : ∃ n, IsEmpty
        (SingularPrefix (blowupDatum (X.fromSpecResidueField x).ker).Y y n),
      height hnew = height hold := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let U := LocalModification.pointComplement x hx
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hdisjoint : Disjoint (U : Set X) ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    exact Set.disjoint_left.mpr fun z hz hz' => hz hz'
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hdisjoint
  let V := B.map ⁻¹ᵁ U
  let v : V.toScheme := ⟨y, hy⟩
  let jY : V.toScheme ⟶ B.Y := V.ι
  let jX : V.toScheme ⟶ X := V.ι ≫ B.map
  let : IsOpenImmersion jX := by
    have hj : jX = (B.map ∣_ U) ≫ U.ι := (morphismRestrict_ι B.map U).symm
    rw [hj]
    infer_instance
  have hY : IsClosed ({jY v} : Set B.Y) := hclosed
  have hX : IsClosed ({jX v} : Set X) := himage
  have hV : ∃ n, IsEmpty (SingularPrefix V.toScheme v n) :=
    (exists_empty_singularPrefix_level_iff jX v hX).mpr hold
  have hnew : ∃ n, IsEmpty (SingularPrefix B.Y y n) :=
    (exists_empty_singularPrefix_level_iff jY v hY).mp hV
  refine ⟨hnew, ?_⟩
  exact (singularHeight_baseChange jY v hY hV hnew).symm.trans
    (singularHeight_baseChange jX v hX hV hold)

private theorem nonregular_pointBlowup_away_iff
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (y : (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (hy : (blowupDatum (X.fromSpecResidueField x).ker).map y ≠ x) :
    (¬ IsRegularLocalRing ((blowupDatum (X.fromSpecResidueField x).ker).Y.presheaf.stalk y)) ↔
      ¬ IsRegularLocalRing
        (X.presheaf.stalk ((blowupDatum (X.fromSpecResidueField x).ker).map y)) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hx y hy
  let e := (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv
  constructor
  · intro hs hr
    let : IsRegularLocalRing (X.presheaf.stalk (B.map y)) := hr
    exact hs (IsRegularLocalRing.of_ringEquiv e)
  · intro hs hr
    let : IsRegularLocalRing (B.Y.presheaf.stalk y) := hr
    exact hs (IsRegularLocalRing.of_ringEquiv e.symm)

/-- Existing finite original heights propagate through the actual singular
point blowup, strictly over the centre and unchanged over its complement. -/
theorem pointBlowup_singularHeight_step
    (S : Type u) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (hS : IsNagataRing.{u, 0} S) (hdS : ringKrullDim S = 2)
    (hRat : NormalModificationH1Vanishing S)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of S)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (hlevels : ∀ z : X, ¬ IsRegularLocalRing (X.presheaf.stalk z) →
      ∃ n, IsEmpty (SingularPrefix X z n)) :
    let B := blowupDatum (X.fromSpecResidueField x).ker
    ∃ hnew : ∀ y : B.Y, ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) →
        ∃ n, IsEmpty (SingularPrefix B.Y y n),
      (∀ y hy (_hbase : B.map y = x), height (hnew y hy) < height (hlevels x hx)) ∧
      (∀ y hy (_haway : B.map y ≠ x),
        ∃ hz : ¬ IsRegularLocalRing (X.presheaf.stalk (B.map y)),
          height (hnew y hy) = height (hlevels (B.map y) hz)) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨_, _, _, hN, hd, hclosed, _, _, _, hR⟩ :=
    singular_stalk_properties_of_rational_model S hS hdS hRat f hX hff x hx
  let B := blowupDatum (X.fromSpecResidueField x).ker
  have hB : NormalStalks B.Y :=
    normalStalks_pointBlowup_of_rational_stalk X hX x hclosed hN hd hR
  have c : PointBlowupChain B.map := by
    have hc : PointBlowupChain (𝟙 B.Y ≫ B.map) :=
      PointBlowupChain.cons x hclosed hd (𝟙 B.Y) (PointBlowupChain.refl B.Y)
    exact Eq.mp (congrArg (fun g : B.Y ⟶ X => PointBlowupChain g)
      (Category.id_comp B.map)) hc
  let : IsIntegral B.Y := c.isIntegral inferInstance
  let : IsProper B.map := c.isProper inferInstance
  let : IsDominant B.map := c.isDominant inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
    c.functionFieldMap_isIso inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (B.map ≫ f))) := by
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  have hclosedY (y : B.Y) (hy : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)) :
      IsClosed ({y} : Set B.Y) :=
    (singular_stalk_properties_of_rational_model S hS hdS hRat (B.map ≫ f)
      hB hcomp y hy).2.2.2.2.2.1
  have hclosedImage (y : B.Y) (hy : ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)) :
      IsClosed ({B.map y} : Set X) := by
    simpa only [Set.image_singleton] using B.map.isClosedMap {y} (hclosedY y hy)
  have hnew : ∀ y : B.Y, ¬ IsRegularLocalRing (B.Y.presheaf.stalk y) →
      ∃ n, IsEmpty (SingularPrefix B.Y y n) := by
    intro y hy
    by_cases hbase : B.map y = x
    · exact child_exists_empty_level (hlevels x hx) ⟨y, hclosedY y hy, hbase, hy⟩
    · have hz := (nonregular_pointBlowup_away_iff x hclosed y hbase).mp hy
      exact (empty_level_and_height_pointBlowup_away x hclosed y hbase
        (hclosedY y hy) (hclosedImage y hy) (hlevels (B.map y) hz)).choose
  refine ⟨hnew, ?_, ?_⟩
  · intro y hy hbase
    exact child_height_lt (hlevels x hx) ⟨y, hclosedY y hy, hbase, hy⟩ (hnew y hy)
  · intro y hy haway
    have hz := (nonregular_pointBlowup_away_iff x hclosed y haway).mp hy
    refine ⟨hz, ?_⟩
    exact (empty_level_and_height_pointBlowup_away x hclosed y haway
      (hclosedY y hy) (hclosedImage y hy) (hlevels (B.map y) hz)).choose_spec

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
