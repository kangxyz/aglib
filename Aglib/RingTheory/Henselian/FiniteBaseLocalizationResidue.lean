/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteBaseLocalizationGenerators

/-!
# The closed-fibre prime after actual coefficient localization

The extended prime contracts to the maximal ideal of the localized coefficient
ring. Consequently its quotient receives the actual residue-field action.
-/

@[expose] public noncomputable section
universe u v
namespace FiniteBaseLocalization

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsPrime]
variable (hq : q.comap (algebraMap R B) = p)

include hq

/-- The selected prime lies in the closed fibre over the localized base. -/
theorem selectedPrime_comap_base :
    (selectedPrime p q).comap
        (algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  have heq : ((selectedPrime p q).comap
      (algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p))).comap
        (algebraMap R (Localization.AtPrime p)) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R B (BaseLocalized (B := B) p), ← Ideal.comap_comap,
      selectedPrime_comap p q hq]
    exact hq
  rw [← IsLocalization.map_under p.primeCompl (Localization.AtPrime p)
    ((selectedPrime p q).comap
      (algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p)))]
  change Ideal.map (algebraMap R (Localization.AtPrime p))
    (((selectedPrime p q).comap
      (algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p))).comap
        (algebraMap R (Localization.AtPrime p))) = _
  rw [heq, Localization.AtPrime.map_eq_maximalIdeal]

end FiniteBaseLocalization
