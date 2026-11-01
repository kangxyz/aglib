/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImagePartitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.NoetherianInduction

/-! # Native constructibility through reduced closed-support partitions

The geometric constructor supplies actual finite strata. Their original inverse
images are identified by the existing composition comparison and C4's partition
criterion detects constructibility. The generic-open premise remains explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Actual nonempty-open constructibility on every reduced closed restriction
implies constructibility on a Noetherian scheme. -/
theorem isConstructible_of_noetherian_reducedClosed_open
    {X : Scheme.{u}} [IsNoetherian X] (F : ModuleSheaf R X)
    (hgen : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsClosedImmersion j → IsReduced Y → Nonempty Y →
      ∃ U : Y.Opens, Nonempty U.toScheme ∧
        IsConstructible ((moduleInverseImage R U.ι).obj ((moduleInverseImage R j).obj F))) :
    IsConstructible F := by
  obtain ⟨p, hp⟩ := FiniteLocallyClosedPartition.exists_of_noetherian_reducedClosed_open
    (fun {Y} (j : Y ⟶ X) => IsConstructible ((moduleInverseImage R j).obj F))
    (by
      intro Y j hj hred hY
      obtain ⟨U, hU, hFU⟩ := hgen Y j hj hred hY
      exact ⟨U, hU, (isConstructible_iff_of_iso
        ((moduleInverseImageComp R j U.ι).app F)).mpr hFU⟩)
  exact isConstructible_of_noetherian_partition p hp

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
