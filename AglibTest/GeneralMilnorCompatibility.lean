/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.LowDegree
import Aglib.KTheory.MilnorK.CompatibilityK3
import Lean.Util.CollectAxioms

/-!
# Genuine compatibility of the all-degree and existing Milnor groups

The tests exercise both inverse maps to old K₂ and K₃, symbol normalization,
cross-universe field naturality, and reuse of the original degree-three
residue normalization. The final audit rejects nonstandard axioms in all
current general-Milnor declarations and their dependencies.
-/

open MilnorK

namespace AglibTest.GeneralMilnorCompatibility

universe u v

variable (F : Type u) [Field F]

/-- Degree two agrees with the original tensor quotient in the original coordinate order. -/
theorem pair_normalization (a b : Fˣ) :
    twoEquiv F (symbol ![a, b]) = MilnorK.K2.symbol a b := twoEquiv_symbol F _

/-- The inverse preserves the same coordinate order. -/
theorem pair_inverse_normalization (a b : Fˣ) :
    (twoEquiv F).symm (MilnorK.K2.symbol a b) = symbol ![a, b] :=
  twoEquiv_symm_symbol F a b

/-- The two quotient presentations are actually mutually inverse on all classes. -/
theorem pair_inverse_laws (x : K F 2) (y : MilnorK.K2.Group F) :
    fromOldK2 F (toOldK2 F x) = x ∧ toOldK2 F (fromOldK2 F y) = y :=
  ⟨(twoEquiv F).symm_apply_apply x, (twoEquiv F).apply_symm_apply y⟩

/-- Degree three agrees with the original nested tensor quotient. -/
theorem triple_normalization (a b c : Fˣ) :
    threeEquiv F (symbol ![a, b, c]) = MilnorK.K3.symbol3 a b c := threeEquiv_symbol F _

/-- The reverse triple-symbol map is explicit. -/
theorem triple_inverse_normalization (a b c : Fˣ) :
    (threeEquiv F).symm (MilnorK.K3.symbol3 a b c) = symbol ![a, b, c] :=
  threeEquiv_symm_symbol F a b c

/-- The degree-three comparison is inverse on every old and new class. -/
theorem triple_inverse_laws (x : K F 3) (y : MilnorK.K3.Group F) :
    fromOldK3 F (toOldK3 F x) = x ∧ toOldK3 F (fromOldK3 F y) = y :=
  ⟨(threeEquiv F).symm_apply_apply x, (threeEquiv F).apply_symm_apply y⟩

variable {F} {E : Type v} [Field E]

/-- Degree-two naturality uses the independently existing field map. -/
theorem pair_field_compatibility (f : F →+* E) (x : K F 2) :
    twoEquiv E (map 2 f x) = MilnorK.K2.map f (twoEquiv F x) := twoEquiv_map f x

/-- Degree-three naturality likewise uses the original field map. -/
theorem triple_field_compatibility (f : F →+* E) (x : K F 3) :
    threeEquiv E (map 3 f x) = MilnorK.K3.map f (threeEquiv F x) := threeEquiv_map f x

/-- Existing tame residue normalization transports to the new groups without a new premise. -/
theorem old_residue_transports (d : MilnorK.K2.DiscreteResidueData F E)
    (hd : MilnorK.K2.UnitReductionCompatible d) (a b : Fˣ)
    (ha : d.value (Additive.ofMul a) = 0) (hb : d.value (Additive.ofMul b) = 0) :
    (twoEquiv E).symm
      (MilnorK.K3.residue3 d hd (threeEquiv F (symbol ![d.uniformizer, a, b]))) =
      symbol ![(d.unitPart (Additive.ofMul a)).toMul,
        (d.unitPart (Additive.ofMul b)).toMul] := by
  rw [triple_normalization, MilnorK.K3.residue3_uniformizer_units d hd a b ha hb,
    twoEquiv_symm_symbol]

end AglibTest.GeneralMilnorCompatibility

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
    throwError "The general Milnor compatibility audit requires legacy imports"
  let libraryPrefix := `MilnorK
  let consumerPrefix := `AglibTest.GeneralMilnorCompatibility
  let isLibrary (name : Name) : Bool := libraryPrefix.isPrefixOf name
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || isLibrary name || consumerPrefix.isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    let libraryOrigin := isLibraryModule env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if libraryOrigin || isLibrary name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "General Milnor declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} general Milnor compatibility and consumer declarations: \
    only standard Lean logical foundations."
