/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.SeparablyClosedResidue
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The prescribed base point of the geometric neighborhood ring

The contraction of the actual maximal ideal is the kernel of the specified
field-valued base point. The map from that prime localization is constructed
by the localization universal property and is proved local. No identification
of the residue extension with a prescribed separable closure is assumed.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace GeometricEtaleColimit

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The prime selected on the original base by the chosen field-valued point. -/
abbrev basePointIdeal : Ideal R := RingHom.ker (algebraMap R Ω)

instance : (basePointIdeal R Ω).IsPrime := RingHom.ker_isPrime _

/-- The constructed local ring lies over exactly the prescribed base point. -/
lemma maximalIdeal_under_base :
    (maximalIdeal (GeometricEtaleColimit R Ω)).under R = basePointIdeal R Ω := by
  rw [maximalIdeal_eq_ker_residue]
  ext r
  change residue R Ω (algebraMap R (GeometricEtaleColimit R Ω) r) = 0 ↔
    algebraMap R Ω r = 0
  rw [(residue R Ω).commutes]

/-- The original base map inverts exactly the elements outside the chosen prime. -/
lemma isUnit_algebraMap_iff_not_mem_basePointIdeal (r : R) :
    IsUnit (algebraMap R (GeometricEtaleColimit R Ω) r) ↔ r ∉ basePointIdeal R Ω := by
  rw [isUnit_iff_residue_ne_zero]
  change residue R Ω (algebraMap R (GeometricEtaleColimit R Ω) r) ≠ 0 ↔
    algebraMap R Ω r ≠ 0
  rw [(residue R Ω).commutes]

/-- The actual map from the prescribed prime localization to the neighborhood ring. -/
def baseLocalizationMap : Localization.AtPrime (basePointIdeal R Ω) →ₐ[R]
    GeometricEtaleColimit R Ω :=
  IsLocalization.liftAlgHom (f := Algebra.ofId R (GeometricEtaleColimit R Ω))
    (fun s : (basePointIdeal R Ω).primeCompl =>
      (isUnit_algebraMap_iff_not_mem_basePointIdeal R Ω s).mpr s.property)

lemma baseLocalizationMap_algebraMap (r : R) :
    baseLocalizationMap R Ω (algebraMap R (Localization.AtPrime (basePointIdeal R Ω)) r) =
      algebraMap R (GeometricEtaleColimit R Ω) r :=
  IsLocalization.lift_eq _ _

/-- The constructed prime-localization map reflects units. -/
instance baseLocalizationMap_isLocalHom : IsLocalHom (baseLocalizationMap R Ω).toRingHom := by
  constructor
  intro x hx
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (basePointIdeal R Ω).primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff _ _ r s).mpr
  apply (isUnit_algebraMap_iff_not_mem_basePointIdeal R Ω r).mp
  have hs := (IsLocalization.map_units (Localization.AtPrime (basePointIdeal R Ω)) s).map
    (baseLocalizationMap R Ω).toRingHom
  have hu := hx.mul hs
  rw [← map_mul, IsLocalization.mk'_spec] at hu
  change IsUnit (baseLocalizationMap R Ω
    (algebraMap R (Localization.AtPrime (basePointIdeal R Ω)) r)) at hu
  rwa [baseLocalizationMap_algebraMap] at hu

/-- The chosen field-valued point after restriction to the source localization. -/
def baseLocalizationPoint : Localization.AtPrime (basePointIdeal R Ω) →ₐ[R] Ω :=
  (residue R Ω).comp (baseLocalizationMap R Ω)

lemma baseLocalizationPoint_algebraMap (r : R) :
    baseLocalizationPoint R Ω
      (algebraMap R (Localization.AtPrime (basePointIdeal R Ω)) r) = algebraMap R Ω r := by
  change residue R Ω (baseLocalizationMap R Ω
    (algebraMap R (Localization.AtPrime (basePointIdeal R Ω)) r)) = _
  rw [baseLocalizationMap_algebraMap, AlgHom.commutes]

end GeometricEtaleColimit
