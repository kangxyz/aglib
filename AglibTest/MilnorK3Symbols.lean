/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.Symbols
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit of degree-three symbol algebra

These consumers use the actual original K₂ and nested K₃ quotients. In
particular, the fixed-last map acts on arbitrary K₂ classes; its first-pair
Steinberg relation is proved at descent, rather than supplied as a premise.
The final regression checks the complete Euclidean identity and repeated
entries retain the sign symbol. Legacy imports expose private helpers to the
standard-logical-axioms-only dependency audit.
-/

open MilnorK.K2 MilnorK.K3

namespace AglibTest.MilnorK3Symbols

variable {K : Type*} [Field K]

/-- Fixing the last unit produces a map on all actual degree-two classes. -/
theorem fixed_last_is_linear (c : Kˣ) (x y : MilnorK.K2.Group K) (n : ℤ) :
    symbol3FixedLast c (x + n • y) =
      symbol3FixedLast c x + n • symbol3FixedLast c y := by
  rw [map_add, map_smul]

/-- The descended map evaluates to literal degree-three quotient symbols. -/
theorem fixed_last_symbol_value (a b c : Kˣ) :
    symbol3FixedLast c (symbol a b) = symbol3 a b c :=
  symbol3FixedLast_symbol c a b

/-- The fixed-last lift needs no hypothesis beyond the original Steinberg sum. -/
theorem fixed_last_steinberg (a b c : Kˣ) (h : (a : K) + (b : K) = 1) :
    symbol3FixedLast c (symbol a b) = 0 := by
  rw [steinberg a b h, map_zero]

/-- Both adjacent exchanges carry a negative sign. -/
theorem both_adjacent_skew (a b c : Kˣ) :
    symbol3 a b c = -symbol3 b a c ∧ symbol3 a b c = -symbol3 a c b :=
  ⟨symbol3_skew_left a b c, symbol3_skew_right a b c⟩

/-- Both cyclic rotations carry a positive sign. -/
theorem both_cyclic_rotations (a b c : Kˣ) :
    symbol3 a b c = symbol3 c a b ∧ symbol3 a b c = symbol3 b c a :=
  ⟨symbol3_cyclic a b c, symbol3_cyclic_left a b c⟩

/-- A unit and its negative vanish in either adjacent pair. -/
theorem both_negative_self_relations (a b : Kˣ) :
    symbol3 a (-a) b = 0 ∧ symbol3 a b (-b) = 0 :=
  ⟨symbol3_self_neg_left a b, symbol3_self_neg_right a b⟩

/-- Repeated entries retain the sign terms in both adjacent pairs. -/
theorem repeated_entry_signs (a b : Kˣ) :
    symbol3 a a b = symbol3 a (-1) b ∧
      symbol3 a b b = symbol3 a b (-1) :=
  ⟨symbol3_self_left a b, symbol3_self_right a b⟩

/-- The identity unit gives zero in all three positions. -/
theorem all_identity_positions (a b : Kˣ) :
    symbol3 1 a b = 0 ∧ symbol3 a 1 b = 0 ∧ symbol3 a b 1 = 0 :=
  ⟨symbol3_one_left a b, symbol3_one_middle a b, symbol3_one_right a b⟩

/-- Multiplicative inversion negates the symbol in every position. -/
theorem all_inverse_positions (a b c : Kˣ) :
    symbol3 a⁻¹ b c = -symbol3 a b c ∧
      symbol3 a b⁻¹ c = -symbol3 a b c ∧
      symbol3 a b c⁻¹ = -symbol3 a b c :=
  ⟨symbol3_inv_left a b c, symbol3_inv_middle a b c, symbol3_inv_right a b c⟩

/-- Division expands as subtraction in every position. -/
theorem all_division_positions (a a' b b' c c' : Kˣ) :
    symbol3 (a / a') b c = symbol3 a b c - symbol3 a' b c ∧
      symbol3 a (b / b') c = symbol3 a b c - symbol3 a b' c ∧
      symbol3 a b (c / c') = symbol3 a b c - symbol3 a b c' :=
  ⟨symbol3_div_left a a' b c, symbol3_div_middle a b b' c,
    symbol3_div_right a b c c'⟩

/-- The Euclidean reduction includes its repeated-entry correction. -/
theorem euclidean_first_pair (p q r b : Kˣ) (h : (p : K) + (r : K) = q) :
    symbol3 p q b = symbol3 p r b - symbol3 q r b + symbol3 q (-1) b :=
  symbol3_euclidean p q r b h

/-- Cyclicity transports the same reduction to the last pair without changing sign. -/
theorem euclidean_last_pair (a p q r : Kˣ) (h : (p : K) + (r : K) = q) :
    symbol3 a p q = symbol3 a p r - symbol3 a q r + symbol3 a q (-1) := by
  simpa only [symbol3_cyclic] using symbol3_euclidean p q r a h

end AglibTest.MilnorK3Symbols

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
    throwError "The Milnor K₃ symbol audit requires legacy imports to include private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3]
  let consumerPrefix := `AglibTest.MilnorK3Symbols
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
        throwError "Milnor K₃ symbol audit declaration {name} is missing \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃ and symbol consumer declarations, \
    including private helpers: only standard Lean logical foundations."
