/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Change
import Aglib.KTheory.MilnorK.Residue.Compatibility
import Lean.Util.CollectAxioms

/-! Direct consumers of coordinate change, its exact last-slot sign, the boundary
degrees, and agreement with the original degree-two and degree-three maps. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueChange

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]
variable (d d' : MilnorK.K2.DiscreteResidueData L κ)
variable (hd : MilnorK.K2.UnitReductionCompatible d) (hd' : MilnorK.K2.UnitReductionCompatible d')
variable (e : Additive κˣ)
variable (hvalue : ∀ a, d'.value a = d.value a)
variable (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e)

/-- The zeroth specialization remains the same with no coordinate-change assumptions. -/
theorem degree_zero_specialization : specialize d' hd' 0 = specialize d hd 0 :=
  specialize_zero_eq d d' hd hd'

include hd hvalue hunit in
/-- The first residue remains the original integer valuation after coordinate change. -/
theorem degree_zero_residue (x : K L 1) :
    zeroEquiv κ (residue d' hd' 0 x) = d.value (oneEquiv L x) := by
  rw [residue_eq_of_unitPart_change d d' hd hd' e hvalue hunit 0]
  exact zeroEquiv_residue d hd x

include hunit in
/-- The first specialization records the actual unit-part change on every source unit. -/
theorem degree_one_specialization (a : Lˣ) :
    oneEquiv κ (specialize d' hd' 1 (symbol ![a])) =
      d.unitPart (Additive.ofMul a) - d.value (Additive.ofMul a) • e := by
  simp only [specialize_symbol, oneEquiv_symbol]
  exact hunit (Additive.ofMul a)

include hunit in
/-- The original uniformizer detects that specialization itself is not independent. -/
theorem changed_uniformizer :
    oneEquiv κ (specialize d' hd' 1 (symbol ![d.uniformizer])) = -e := by
  rw [degree_one_specialization d d' hd' e hunit, d.unitPart_uniformizer,
    d.value_uniformizer, one_smul, zero_sub]

include hd hvalue hunit in
/-- In residue degree one the changed construction agrees with the original tame map. -/
theorem degree_one_residue (x : K L 2) :
    oneEquiv κ (residue d' hd' 1 x) = MilnorK.K2.tame d (twoEquiv L x) := by
  rw [residue_eq_of_unitPart_change d d' hd hd' e hvalue hunit 1]
  exact oneEquiv_residue_one d hd x

include hunit in
/-- The positive-degree correction uses right multiplication and the negative sign. -/
theorem full_specialization_change (n : ℕ) (x : K L (n + 1)) :
    specialize d' hd' (n + 1) x = specialize d hd (n + 1) x -
      productUnit n (residue d hd n x) e :=
  specialize_change_apply d d' hd hd' e hunit n x

include hvalue hunit in
/-- All residues, on arbitrary classes, are independent of this normalized change. -/
theorem full_residue_change (n : ℕ) (x : K L (n + 1)) :
    residue d' hd' n x = residue d hd n x :=
  LinearMap.congr_fun (residue_eq_of_unitPart_change d d' hd hd' e hvalue hunit n) x

include hunit in
/-- The specialization correction agrees exactly with the original K₂ convention. -/
theorem old_specialization_change (x : K L 2) :
    twoEquiv κ (specialize d' hd' 2 x) = twoEquiv κ (specialize d hd 2 x) -
      MilnorK.K2.symbolBilinear κ (MilnorK.K2.tame d (twoEquiv L x)) e := by
  rw [specialize_change_apply d d' hd hd' e hunit 1, map_sub,
    twoEquiv_productUnit, oneEquiv_residue_one]

include hunit in
/-- In left-slot notation the same correction is the original positive `{e,∂x}`. -/
theorem old_source_convention (x : K L 2) :
    MilnorK.K2.specialize d' hd' (twoEquiv L x) -
        MilnorK.K2.specialize d hd (twoEquiv L x) =
      MilnorK.K2.symbolBilinear κ e (MilnorK.K2.tame d (twoEquiv L x)) := by
  have h := old_specialization_change d d' hd hd' e hunit x
  rw [twoEquiv_specialize, twoEquiv_specialize, MilnorK.K2.bilinear_symbol_skew] at h
  rw [h]
  abel

include hvalue hunit in
/-- The unchanged degree-three construction is the original cyclic residue map. -/
theorem old_degree_three_residue (x : K L 3) :
    twoEquiv κ (residue d' hd' 2 x) = MilnorK.K3.residue3 d hd (threeEquiv L x) := by
  rw [residue_eq_of_unitPart_change d d' hd hd' e hvalue hunit 2]
  exact twoEquiv_residue_two d hd x

/-- The key diagonal sign holds after every prefix, including the empty prefix. -/
theorem diagonal_sign (n : ℕ) (x : K κ n) :
    productUnit (n + 1) (productUnit n x e) e =
      -productUnit (n + 1) (productUnit n x (MilnorK.K2.residueSign κ)) e :=
  productUnit_pair_self n x e

include hunit in
/-- The correction vanishes precisely as required on the actual residue kernel. -/
theorem residue_kernel_specialization (n : ℕ) (x : K L (n + 1))
    (hx : residue d hd n x = 0) :
    specialize d' hd' (n + 1) x = specialize d hd (n + 1) x :=
  specialize_eq_on_residue_kernel d d' hd hd' e hunit n x hx

end AglibTest.GeneralMilnorResidueChange

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName)
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueChange]
  let selectedDeclaration (name : Name) := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} residue-change and general Milnor declarations: \
    standard axioms only."
