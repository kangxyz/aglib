/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.PrimitiveRoots
public import Aglib.RingTheory.Henselian.StrictHenselization.LocalStages
public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue
public import Aglib.RingTheory.Henselian.PrimitiveRoots

/-! # Primitive roots at the same original pointed local stage

Choose one primitive root in the actual strictly local neighborhood colimit,
descend it after any prescribed stage, and retain its order in that stage's
native point localization by the original map back to the same colimit.
No injectivity or domain condition is used, and arbitrary localization is
not asserted to preserve primitive roots.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace GeometricEtaleColimit

universe u

/-- One original primitive root descends to a genuine neighborhood and stays
primitive in its specified point localization, with its exact colimit image. -/
theorem exists_primitiveRoot_pointLocalization_over
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (X : GeometricEtaleNeighborhood R Ω) :
    ∃ (ζ : GeometricEtaleColimit R Ω), IsPrimitiveRoot ζ n ∧
      ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X ⟶ Y) (a : Y.algebra),
        ι R Ω Y a = ζ ∧ IsPrimitiveRoot a n ∧
        IsPrimitiveRoot (algebraMap Y.algebra (stageLocalRing R Ω Y) a) n := by
  have hunitC : IsUnit (n : GeometricEtaleColimit R Ω) := by
    simpa only [map_natCast] using hunit.map (algebraMap R (GeometricEtaleColimit R Ω))
  obtain ⟨ζ, hζ⟩ := HenselianLocalRing.exists_primitiveRoot_of_isSepClosed_residue
    (GeometricEtaleColimit R Ω) n hn hunitC
  obtain ⟨Y, g, a, ha, hpa⟩ := exists_primitiveRoot_rep_over R Ω hζ X
  refine ⟨ζ, hζ, Y, g, a, ha, hpa, ?_⟩
  constructor
  · rw [← map_pow, hpa.pow_eq_one, map_one]
  · intro m hm
    apply hζ.dvd_of_pow_eq_one m
    rw [← ha, ← stageLocalMap_algebraMap R Ω Y a, ← map_pow, hm, map_one]

end GeometricEtaleColimit
