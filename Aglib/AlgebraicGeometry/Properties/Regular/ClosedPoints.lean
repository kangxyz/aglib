/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Detecting regular stalks at closed points

Regularity of an actual scheme stalk passes to its generizations through the
original map from its local spectrum. On a quasi-compact scheme it therefore
suffices to check closed points. For a proper morphism to a local spectrum,
regularity on the literal closed fibre suffices.

The local contraction construction is the current consumer. No openness of the
regular locus, excellence, global Noetherianity or coefficient field is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Regularity of an actual stalk passes to every generization of its point. -/
theorem isRegularLocalRing_stalk_of_specializes
    {X : Scheme.{u}} {x y : X} (hxy : x ⤳ y)
    (hy : IsRegularLocalRing (X.presheaf.stalk y)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have hx : x ∈ Set.range (X.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]
    exact hxy
  obtain ⟨z, rfl⟩ := hx
  let : IsRegularLocalRing (X.presheaf.stalk y) := hy
  let : Flat (X.fromSpecStalk y) := fromSpecStalk_flat X y
  let : IsIso ((X.fromSpecStalk y).stalkMap z) :=
    Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks (X.fromSpecStalk y) z
  let : z.asIdeal.IsPrime := z.2
  let : IsRegularLocalRing (Localization.AtPrime z.asIdeal) :=
    IsRegularLocalRing.atPrime (X.presheaf.stalk y) z.asIdeal
  let : IsRegularLocalRing ((Spec (X.presheaf.stalk y)).presheaf.stalk z) :=
    IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (X.presheaf.stalk y) z).commRingCatIsoToRingEquiv.symm
  exact
    IsRegularLocalRing.of_ringEquiv
      (asIso ((X.fromSpecStalk y).stalkMap z)).commRingCatIsoToRingEquiv.symm

/-- On a quasi-compact scheme, regularity of closed-point stalks suffices. -/
theorem regularStalks_of_regular_closedPoints
    (X : Scheme.{u}) [CompactSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x)) : RegularStalks X := by
  intro x
  obtain ⟨y, hy, hyclosed⟩ := isClosed_closure.exists_closed_singleton
    (show (closure ({x} : Set X)).Nonempty from ⟨x, subset_closure (by simp)⟩)
  exact isRegularLocalRing_stalk_of_specializes
    (specializes_iff_mem_closure.mpr hy) (h y hyclosed)

/-- A closed point of a proper scheme over a local spectrum lies on its
literal closed fibre. -/
theorem image_closedPoint_eq_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    f x = IsLocalRing.closedPoint R := by
  have hc : IsClosed ({f x} : Set (Spec (CommRingCat.of R))) := by
    simpa only [Set.image_singleton] using f.isClosedMap _ hx
  exact (Set.mem_singleton_iff.mp
    ((IsLocalRing.specializes_closedPoint (f x)).mem_closed hc
      (Set.mem_singleton (f x)))).symm

/-- A proper scheme over a local spectrum is regular if its actual stalks
are regular at every point of the literal closed fibre. -/
theorem regularStalks_of_regular_closedFibre
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (h : ∀ x : X, f x = IsLocalRing.closedPoint R →
      IsRegularLocalRing (X.presheaf.stalk x)) : RegularStalks X := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact regularStalks_of_regular_closedPoints X fun x hx ↦
    h x (image_closedPoint_eq_closedPoint f x hx)

end AlgebraicGeometry.Scheme
