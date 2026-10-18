/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.Residue
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit of the actual Milnor K₃ residue

The tests retain explicit elementary valuation/reduction data, check the exact
nested quotient, descent, normalization, and repeated-uniformizer signs.
Legacy imports allow the audit to inspect the full K₂/K₃ implementation closure,
including private helpers. No finite norm, reciprocity, or realization premise is used.
-/

open MilnorK.K2 MilnorK.K3

namespace AglibTest.MilnorK3Residue

variable (K : Type*) [Field K]

/-- Degree three uses the original degree-two quotient as its second tensor factor. -/
theorem actual_nested_quotient :
    MilnorK.K3.Group K = (TensorProduct ℤ (Additive Kˣ) (MilnorK.K2.Group K) ⧸
      Submodule.span ℤ (MilnorK.K3.steinbergGenerators K)) := rfl

/-- Symbols are literally pure tensors mapped into the new quotient. -/
theorem actual_symbol3 (a b c : Kˣ) :
    symbol3 a b c = (R3 K).mkQ
      (TensorProduct.tmul ℤ (Additive.ofMul a) (symbol b c)) := rfl

/-- Both adjacent Steinberg pairs vanish in the constructed quotient. -/
theorem both_steinberg_relations (a b c : Kˣ) :
    ((a : K) + (b : K) = 1 → symbol3 a b c = 0) ∧
      ((b : K) + (c : K) = 1 → symbol3 a b c = 0) :=
  ⟨symbol3_steinberg_left a b c, symbol3_steinberg_right a b c⟩

/-- All three multiplicative additivity laws hold for actual symbols. -/
theorem three_additivity_relations (a a' b b' c c' : Kˣ) :
    symbol3 (a * a') b c = symbol3 a b c + symbol3 a' b c ∧
      symbol3 a (b * b') c = symbol3 a b c + symbol3 a b' c ∧
      symbol3 a b (c * c') = symbol3 a b c + symbol3 a b c' :=
  ⟨symbol3_mul_left a a' b c, symbol3_mul_middle a b b' c,
    symbol3_mul_right a b c c'⟩

variable {K} {k : Type*} [Field k]
variable (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d)

/-- The precursor contains its essential valuation-times-sign correction. -/
theorem sign_correct_precursor (a : UnitsAdd K) (x : MilnorK.K2.Group K) :
    residue3Bilinear d hd a x = d.value a • specialize d hd x +
      symbolBilinear k (d.unitPart a - d.value a • residueSign k) (tame d x) :=
  residue3Bilinear_apply d hd a x

/-- The nontrivial cyclic law holds before descent. -/
theorem precursor_cyclic (a b c : Kˣ) :
    residue3Bilinear d hd (Additive.ofMul a) (symbol b c) =
      residue3Bilinear d hd (Additive.ofMul c) (symbol a b) :=
  residue3Bilinear_cyclic d hd a b c

/-- The actual quotient map has the proved symbol formula. -/
theorem actual_residue_formula (a b c : Kˣ) :
    residue3 d hd (symbol3 a b c) =
      d.value (Additive.ofMul a) • specialize d hd (symbol b c) +
        symbolBilinear k
          (d.unitPart (Additive.ofMul a) - d.value (Additive.ofMul a) • residueSign k)
          (tame d (symbol b c)) := rfl

/-- Symbols of three valuation units are unramified. -/
theorem three_units_vanish (a b c : Kˣ)
    (ha : d.value (Additive.ofMul a) = 0) (hb : d.value (Additive.ofMul b) = 0)
    (hc : d.value (Additive.ofMul c) = 0) :
    residue3 d hd (symbol3 a b c) = 0 := residue3_units d hd a b c ha hb hc

/-- First-slot normalization is the literal symbol of the reduced units. -/
theorem literal_normalization (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    residue3 d hd (symbol3 d.uniformizer u v) =
      symbol (d.unitPart (Additive.ofMul u)).toMul (d.unitPart (Additive.ofMul v)).toMul :=
  residue3_uniformizer_units d hd u v hu hv

/-- The same normalization holds with the uniformizer last in degree three. -/
theorem last_slot_normalization (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    residue3 d hd (symbol3 u v d.uniformizer) =
      symbol (d.unitPart (Additive.ofMul u)).toMul (d.unitPart (Additive.ofMul v)).toMul := by
  rw [residue3_cyclic, residue3_uniformizer_units d hd u v hu hv]

/-- Two uniformizers expose the sign correction that an unsigned formula would lose. -/
theorem repeated_uniformizer_sign (u : Kˣ) (hu : d.value (Additive.ofMul u) = 0) :
    residue3 d hd (symbol3 d.uniformizer d.uniformizer u) =
      symbolBilinear k (residueSign k) (d.unitPart (Additive.ofMul u)) :=
  residue3_uniformizer_uniformizer_unit d hd u hu

/-- Three uniformizers retain the sign pairing, with both equivalent signs checked. -/
theorem triple_uniformizer_sign :
    residue3 d hd (symbol3 d.uniformizer d.uniformizer d.uniformizer) =
        -symbolBilinear k (residueSign k) (residueSign k) ∧
      residue3 d hd (symbol3 d.uniformizer d.uniformizer d.uniformizer) =
        symbolBilinear k (residueSign k) (residueSign k) :=
  ⟨residue3_uniformizer_three d hd, residue3_uniformizer_three_sign d hd⟩

end AglibTest.MilnorK3Residue

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
    throwError "The Milnor K₃ audit requires legacy imports to include private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3]
  let consumerPrefix := `AglibTest.MilnorK3Residue
  let isLibrary (name : Name) : Bool := libraryPrefixes.any (·.isPrefixOf name)
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
        throwError "Milnor K₃ audit declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃ and degree-three consumer declarations, \
    including private helpers: only standard Lean logical foundations."
