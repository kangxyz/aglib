/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.TupleSymbols
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-!
# Arbitrary-coordinate symbol consumers and rejecting axiom audit

These consumers use the actual all-degree quotient and the actual degree-two
quotient map. They cover separated positions, the reverse coordinate order,
movement to the final slot, retained repeated-entry signs, and characteristic
two. The rejecting dependency audit includes the private distance-induction
and tuple-transposition helpers through legacy imports.
-/

open MilnorK

namespace AglibTest.GeneralMilnorTupleSymbols

universe u

variable {F : Type u} [Field F] {n : ℕ}

/-- Pair insertion acts linearly on arbitrary actual degree-two classes. -/
theorem arbitrary_pair_linear (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (x y : MilnorK.K2.Group F) (z : ℤ) :
    pairMap a i j hij (x + z • y) = pairMap a i j hij x + z • pairMap a i j hij y := by
  rw [map_add, map_smul]

/-- Pair insertion has literal substitution values, in arbitrary degree and universe. -/
theorem arbitrary_pair_value (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b c : Fˣ) :
    pairMap a i j hij (MilnorK.K2.symbol b c) =
      symbol (Function.update (Function.update a i b) j c) := pairMap_symbol a i j hij b c

/-- The lifted map needs only the standard degree-two Steinberg condition. -/
theorem arbitrary_pair_steinberg (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b c : Fˣ) (h : (b : F) + (c : F) = 1) :
    symbol (Function.update (Function.update a i b) j c) = 0 := by
  rw [← pairMap_symbol a i j hij, MilnorK.K2.steinberg b c h, map_zero]

/-- A separated pair in degree four is genuinely skew, with all intervening entries fixed. -/
theorem separated_four_positions (a : SymbolTuple F 4) :
    symbol a = -symbol (Function.update (Function.update a 0 (a 3)) 3 (a 0)) :=
  symbol_skew a 0 3 (by decide)

/-- The reverse order of a separated pair gives the same insertion identity. -/
theorem reversed_four_positions (a : SymbolTuple F 4) (b c : Fˣ) :
    symbol (Function.update (Function.update a 3 b) 0 c) =
      -symbol (Function.update (Function.update a 3 c) 0 b) :=
  symbol_update_skew a 3 0 (by decide) b c

/-- Any chosen non-final coordinate can be moved into the final position in one swap. -/
theorem move_to_final_position (a : SymbolTuple F (n + 1)) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    symbol a = -symbol
      (Function.update (Function.update a i (a (Fin.last n))) (Fin.last n) (a i)) :=
  symbol_skew a i (Fin.last n) hi

/-- A non-adjacent Steinberg pair vanishes without a relation imposed at that pair. -/
theorem separated_steinberg (a : SymbolTuple F 4) (h : (a 0 : F) + (a 3 : F) = 1) :
    symbol a = 0 := steinberg_of_ne a 0 3 (by decide) h

/-- The sign contribution is retained for repetitions at separated coordinates. -/
theorem separated_repeated_entry (a : SymbolTuple F 4) (b : Fˣ) :
    symbol (Function.update (Function.update a 0 b) 3 b) =
      symbol (Function.update (Function.update a 0 b) 3 (-1)) :=
  symbol_update_self a 0 3 (by decide) b

/-- Opposite entries vanish at separated coordinates in the reverse order as well. -/
theorem separated_opposite_entry (a : SymbolTuple F 4) (b : Fˣ) :
    symbol (Function.update (Function.update a 3 b) 0 (-b)) = 0 :=
  symbol_update_self_neg a 3 0 (by decide) b

/-- The same arbitrary-coordinate construction works in characteristic two. -/
theorem characteristic_two_pair (a : SymbolTuple (ZMod 2) 4) (b c : (ZMod 2)ˣ) :
    pairMap a 3 0 (by decide) (MilnorK.K2.symbol b c) =
      symbol (Function.update (Function.update a 3 b) 0 c) :=
  pairMap_symbol a 3 0 (by decide) b c

end AglibTest.GeneralMilnorTupleSymbols

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
    throwError "The arbitrary-coordinate audit requires legacy imports to include private helpers"
  let libraryPrefixes := #[`MilnorK, `MilnorK.K2]
  let consumerPrefix := `AglibTest.GeneralMilnorTupleSymbols
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
        throwError "Arbitrary-coordinate declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} general Milnor, degree-two, and arbitrary-coordinate consumer \
    declarations, including private helpers: only standard Lean logical foundations."
