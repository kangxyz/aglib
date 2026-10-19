/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity of scheme stalks

Regularity is imposed on the actual local rings of a scheme. For an affine scheme with a
Noetherian coordinate ring, this agrees with `IsRegularRing` through the canonical
stalk-localization isomorphisms.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A scheme has regular stalks if all its actual local rings are regular local rings. -/
def RegularStalks (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- Regularity of stalks restricts along an open immersion. -/
theorem RegularStalks.of_isOpenImmersion {X Y : Scheme.{u}} (hY : RegularStalks Y)
    (f : X ⟶ Y) [IsOpenImmersion f] : RegularStalks X := by
  intro x
  let := hY (f x)
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

instance : ObjectProperty.IsClosedUnderIsomorphisms RegularStalks where
  of_iso e h := h.of_isOpenImmersion e.inv

/-- The spectrum of a regular ring has regular actual stalks. -/
theorem regularStalks_spec (R : Type u) [CommRing R] [IsRegularRing R] :
    RegularStalks (Spec (.of R)) := by
  intro x
  let : x.asIdeal.IsPrime := x.2
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of R) x).commRingCatIsoToRingEquiv.symm

/-- For a Noetherian ring, regularity can be tested on its actual spectrum stalks. -/
theorem regularStalks_spec_iff (R : Type u) [CommRing R] [IsNoetherianRing R] :
    RegularStalks (Spec (.of R)) ↔ IsRegularRing R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ regularStalks_spec R⟩
  rw [isRegularRing_iff]
  intro p hp
  let x : PrimeSpectrum R := ⟨p, hp⟩
  let := h x
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of R) x).commRingCatIsoToRingEquiv

/-- An affine section ring is regular when the ambient scheme has regular stalks and
the section ring is Noetherian. -/
theorem RegularStalks.isRegularRing_sections {X : Scheme.{u}} (hX : RegularStalks X)
    {U : X.Opens} (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsRegularRing Γ(X, U) :=
  (regularStalks_spec_iff Γ(X, U)).mp (hX.of_isOpenImmersion hU.fromSpec)

end AlgebraicGeometry.Scheme
