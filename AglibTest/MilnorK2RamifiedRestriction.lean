/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction
public import Lean.Util.CollectAxioms

/-! # Consumers of actual ramified restriction in Milnor K₂ -/

@[expose] public noncomputable section

namespace AglibTest.MilnorK2RamifiedRestriction

open MilnorK.K2 MilnorK.K2.DVR IsLocalRing

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))
  {πR : R} {πS : S} (hπR : Irreducible πR) (hπS : Irreducible πS)
  (u : Sˣ) (e : ℕ) (hπ : j πR = (u : S) * πS ^ e)

include hF hπR hπS hπ

omit [IsLocalHom j] in
/-- The original integer order is scaled by the literal ramification exponent. -/
theorem original_order_is_scaled (a : Kˣ) :
    value S L (Additive.ofMul (Units.map F.toMonoidHom a)) =
      (e : ℤ) * value R K (Additive.ofMul a) :=
  ramified_value_map j F hF hπR hπS u e hπ (Additive.ofMul a)

/-- The original tame map has the expected restriction formula on every quotient class. -/
theorem original_tame_is_scaled (x : MilnorK.K2.Group K) :
    tame (data (K := L) hπS) (map F x) =
      (e : ℤ) • unitsLinear (ResidueField.map j) (tame (data (K := K) hπR) x) :=
  LinearMap.congr_fun (ramified_tame_restrict j F hF hπR hπS u e hπ) x

/-- The existing specialization convention gives the plus-sign correction. -/
theorem original_specialization_has_correction (x : MilnorK.K2.Group K) :
    specialize (data (K := L) hπS) (unitReductionCompatible hπS) (map F x) =
      map (ResidueField.map j)
          (specialize (data (K := K) hπR) (unitReductionCompatible hπR) x) +
        symbolBilinear (ResidueField S)
          (unitsLinear (ResidueField.map j) (tame (data (K := K) hπR) x))
          (Additive.ofMul (Units.map (residue S).toMonoidHom u)) :=
  LinearMap.congr_fun (ramified_specialize_restrict j F hF hπR hπS u e hπ) x

/-- On the genuine downstairs tame kernel, specialization commutes with ramified restriction. -/
theorem original_tame_kernel_specialization (x : MilnorK.K2.Group K)
    (hx : tame (data (K := K) hπR) x = 0) :
    specialize (data (K := L) hπS) (unitReductionCompatible hπS) (map F x) =
      map (ResidueField.map j)
        (specialize (data (K := K) hπR) (unitReductionCompatible hπR) x) := by
  have h := original_specialization_has_correction j F hF hπR hπS u e hπ x
  simpa only [hx, map_zero, LinearMap.zero_apply, add_zero] using h

/-- Joint upstairs vanishing annihilates tame downstairs and specialization
after residue restriction. -/
theorem original_joint_defects_are_annihilated (x : MilnorK.K2.Group K)
    (ht : tame (data (K := L) hπS) (map F x) = 0)
    (hs : specialize (data (K := L) hπS) (unitReductionCompatible hπS) (map F x) = 0) :
    (e : ℤ) • tame (data (K := K) hπR) x = 0 ∧
      (e : ℤ) • map (ResidueField.map j)
        (specialize (data (K := K) hπR) (unitReductionCompatible hπR) x) = 0 :=
  ramified_joint_kernel_annihilation j F hF hπR hπS u e hπ x ht hs

open Lean in
run_cmd do
  for name in #[``ramificationIndex_pos, ``residueUnitsLinear_injective,
      ``normalizedLift_decomposition, ``ramified_fieldUnits_map,
      ``ramified_uniformizer_map, ``ramified_decomposition, ``ramified_value_map,
      ``ramified_normalizedLift_map, ``ramificationUnitResidue,
      ``ramified_unitResidue_map, ``ramified_unitPart_map,
      ``ramified_tame_restrict, ``ramified_specialize_restrict,
      ``ramified_tame_annihilated, ``ramified_joint_kernel_annihilation,
      ``original_order_is_scaled, ``original_tame_is_scaled,
      ``original_specialization_has_correction, ``original_tame_kernel_specialization,
      ``original_joint_defects_are_annihilated] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual ramified DVR restriction uses only standard Lean logical foundations."

end AglibTest.MilnorK2RamifiedRestriction
