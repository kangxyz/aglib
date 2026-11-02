/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.LocalStages
public import Aglib.RingTheory.RegularLocalRing.EtaleParameter

/-! # Regular parameters at the original pointed etale stage

The actual prime localization selected by a geometric neighborhood's point
retains the original regular parameter. Only this Noetherian local stage is
used: no Noetherianity or domain hypothesis on the neighborhood colimit is
needed. The localization is essentially etale, not asserted finitely presented
or etale. Spreading finite data back to a genuine neighborhood is separate.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace GeometricEtaleNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
  (X : GeometricEtaleNeighborhood R Ω)

/-- The original regular parameter remains a regular parameter in the actual
point localization of a genuine etale neighborhood. Its Noetherian local
regularity and the locality of its original base map are supplied together. -/
theorem regularParameter_pointLocalization (f : R)
    (hf : f ∈ maximalIdeal R) (hreg : IsSMulRegular R f)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})] :
    let S := Localization.ResiduePoint.Ring X.point.toRingHom
    IsLocalHom (algebraMap R S) ∧ IsNoetherianRing S ∧ IsRegularLocalRing S ∧
      algebraMap R S f ∈ maximalIdeal S ∧ IsSMulRegular S (algebraMap R S f) ∧
      IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S f}) := by
  let S := GeometricEtaleColimit.stageLocalRing R Ω X
  let : IsLocalHom (algebraMap R S) :=
    GeometricEtaleColimit.stageLocalRing_base_local R Ω X
  exact ⟨inferInstance, Algebra.FormallyUnramified.regularParameter_of_flat R S f hf hreg⟩

end GeometricEtaleNeighborhood
