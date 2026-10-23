/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.HeightOneIntersection

/-!
# Canonical height-one localization membership

These bridges apply the existing normal Noetherian domain intersection and
divisibility theorems to the actual canonical localizations and algebra maps.
The fraction field remains the original `FractionRing R` throughout.

The current consumer is the vertical Cartier membership argument in
`Aglib.AlgebraicGeometry.Surfaces.Resolution.VerticalCartier`.
-/

@[expose] public section

namespace IsIntegrallyClosed

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- A fraction in the original fraction field which belongs to every actual
height-one localization comes from the original ring. -/
theorem mem_range_of_mem_range_atPrime_height_one (x : FractionRing R)
    (h : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      x ∈ (algebraMap (Localization.AtPrime P) (FractionRing R)).range) :
    x ∈ (algebraMap R (FractionRing R)).range := by
  apply mem_range_of_forall_height_one
  intro P hP hheight
  let : P.IsPrime := hP
  obtain ⟨z, hz⟩ := h P hheight
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
  refine ⟨s, s.property, r, ?_⟩
  have heq : z * algebraMap R (Localization.AtPrime P) s =
      algebraMap R (Localization.AtPrime P) r := by
    rw [← hrs]
    exact IsLocalization.mk'_spec _ r s
  have heq' := congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) heq
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at heq'
  rw [hz] at heq'
  exact heq'.symm

/-- The original ring is the intersection of its actual height-one local
rings inside its original fraction field, as a membership equivalence. -/
theorem mem_range_iff_mem_range_atPrime_height_one (x : FractionRing R) :
    x ∈ (algebraMap R (FractionRing R)).range ↔
      ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        x ∈ (algebraMap (Localization.AtPrime P) (FractionRing R)).range := by
  constructor
  · rintro ⟨r, rfl⟩ P hP _
    exact ⟨algebraMap R (Localization.AtPrime P) r,
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r).symm⟩
  · exact mem_range_of_mem_range_atPrime_height_one x

end IsIntegrallyClosed

namespace Ideal

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- Membership in a nonzero principal ideal is detected after actual
localization at every height-one prime. -/
theorem mem_span_singleton_of_mem_map_atPrime_height_one {a b : R} (ha : a ≠ 0)
    (h : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      algebraMap R (Localization.AtPrime P) b ∈
        (Ideal.span {a}).map (algebraMap R (Localization.AtPrime P))) :
    b ∈ Ideal.span {a} := by
  apply Ideal.mem_span_singleton.mpr
  apply IsIntegrallyClosed.dvd_of_forall_height_one ha
  intro P hP hheight
  let : P.IsPrime := hP
  obtain ⟨s, hs, hsb⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl
      (Localization.AtPrime P) (Ideal.span {a}) b).mp (h P hheight)
  exact ⟨s, hs, Ideal.mem_span_singleton.mp hsb⟩

/-- The exact local membership criterion with its immediate converse. -/
theorem mem_span_singleton_iff_mem_map_atPrime_height_one {a b : R} (ha : a ≠ 0) :
    b ∈ Ideal.span {a} ↔
      ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        algebraMap R (Localization.AtPrime P) b ∈
          (Ideal.span {a}).map (algebraMap R (Localization.AtPrime P)) := by
  exact ⟨fun hb _ _ _ ↦ Ideal.mem_map_of_mem _ hb,
    mem_span_singleton_of_mem_map_atPrime_height_one ha⟩

end Ideal
