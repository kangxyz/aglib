/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood

/-! # The original etale target open retains a whole local section

Etaleness of the original closed fibre over the section point removes the
closed branch image. Every point of the same local section remains in the
canonical target open by specialization; no global purity is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The canonical target etale open of a finite morphism contains the entire
image of a local section once it contains the fibre over its closed point. -/
theorem range_subset_etaleTargetOpen_of_local_closedFiber
    {R : Type u} [CommRing R] [IsLocalRing R]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (s : Spec (.of R) ⟶ X)
    (h : ∀ y : Y, f y = s (IsLocalRing.closedPoint R) → f.etaleAt y) :
    Set.range s ⊆ f.etaleTargetOpen f.isClosedMap := by
  have hc : s (IsLocalRing.closedPoint R) ∈ f.etaleTargetOpen f.isClosedMap := by
    rintro ⟨y, hy, he⟩
    exact hy (h y he)
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open
    (f.etaleTargetOpen f.isClosedMap).isOpen hc

end AlgebraicGeometry.Scheme.Hom
