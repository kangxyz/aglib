/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Symbols
import Aglib.KTheory.MilnorK.CompatibilityK3
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms

/-!
# Genuine product and sign consumers in arbitrary Milnor degrees

The consumers below exercise the two quotient factors, cross-universe field
naturality, honest degree transport, integer degree-zero actions, association,
compatibility with the existing K₂/K₃ symbols, and adjacent sign identities.
The characteristic-two check is the diagonal `-1` formula, not an unsupported
alternation claim. The final audit rejects every nonstandard axiom dependency,
including those of private helpers in the imported general-Milnor modules.
-/

open MilnorK

namespace AglibTest.GeneralMilnorProduct

universe u v

variable (F : Type u) [Field F] (m n p : ℕ)

/-- The product is bilinear on the actual quotient groups. -/
noncomputable def actual_product : K F m →ₗ[ℤ] K F n →ₗ[ℤ] K F (m + n) := product m n

/-- Ordered tuple concatenation is the product normalization in every degree. -/
theorem concatenate_symbols (a : SymbolTuple F m) (b : SymbolTuple F n) :
    product m n (symbol a) (symbol b) = symbol (Fin.append a b) := product_symbol a b

/-- The left multiplicativity relation is killed even against a general right class. -/
theorem left_relation (a : SymbolTuple F m) (i : Fin m) (b c : Fˣ) (y : K F n) :
    product m n (symbol (Function.update a i (b * c)) -
      symbol (Function.update a i b) - symbol (Function.update a i c)) y = 0 := by
  rw [symbol_mul]
  simp

/-- The right multiplicativity relation is killed even against a general left class. -/
theorem right_relation (x : K F m) (a : SymbolTuple F n) (i : Fin n) (b c : Fˣ) :
    product m n x (symbol (Function.update a i (b * c)) -
      symbol (Function.update a i b) - symbol (Function.update a i c)) = 0 := by
  rw [symbol_mul]
  simp

/-- Steinberg vanishing descends in the left quotient factor. -/
theorem left_steinberg (a : SymbolTuple F m) (i j : Fin m)
    (hij : i.val + 1 = j.val) (h : (a i : F) + (a j : F) = 1) (y : K F n) :
    product m n (symbol a) y = 0 := by
  rw [steinberg a i j hij h]
  simp

/-- Steinberg vanishing descends independently in the right quotient factor. -/
theorem right_steinberg (x : K F m) (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : (a i : F) + (a j : F) = 1) :
    product m n x (symbol a) = 0 := by
  rw [steinberg a i j hij h]
  simp

/-- The target quotient also kills a Steinberg pair straddling the concatenation boundary. -/
theorem crossing_steinberg (a : SymbolTuple F (m + 1)) (b : SymbolTuple F (n + 1))
    (h : (a (Fin.last m) : F) + (b 0 : F) = 1) :
    product (m + 1) (n + 1) (symbol a) (symbol b) = 0 := by
  rw [product_symbol]
  apply steinberg _ (Fin.castAdd (n + 1) (Fin.last m)) (Fin.natAdd (m + 1) 0)
  · simp
  · simpa only [Fin.append_left, Fin.append_right] using h

/-- Associativity identifies both genuinely different natural-number parenthesizations. -/
theorem transported_associativity (x : K F m) (y : K F n) (z : K F p) :
    degreeCongr (Nat.add_assoc m n p) (product (m + n) p (product m n x y) z) =
      product m (n + p) x (product n p y z) := product_assoc x y z

/-- Degree zero acts on either side through the proved equivalence with the integers. -/
theorem integer_actions (z : K F 0) (x : K F n) :
    degreeCongr (Nat.zero_add n) (product 0 n z x) = zeroEquiv F z • x ∧
      degreeCongr (Nat.add_zero n) (product n 0 x z) = zeroEquiv F z • x :=
  ⟨product_zero_left z x, product_zero_right x z⟩

/-- The empty tuple gives both unit laws on arbitrary quotient classes. -/
theorem empty_units (x : K F n) :
    degreeCongr (Nat.zero_add n) (product 0 n (symbol Fin.elim0) x) = x ∧
      degreeCongr (Nat.add_zero n) (product n 0 x (symbol Fin.elim0)) = x :=
  ⟨product_empty_left x, product_empty_right x⟩

/-- Transport really reindexes each symbol by the corresponding finite-type equality. -/
theorem symbol_transport (h : m = n) (a : SymbolTuple F m) :
    degreeCongr h (symbol a) = symbol (a ∘ Fin.cast h.symm) := degreeCongr_symbol h a

/-- The one-by-one product agrees with the original degree-two symbol. -/
theorem old_pair_product (a b : Fˣ) :
    twoEquiv F (product 1 1 (symbol ![a]) (symbol ![b])) = MilnorK.K2.symbol a b := by
  rw [product_symbol, twoEquiv_symbol]
  rfl

/-- The one-by-two product agrees with the original ordered degree-three symbol. -/
theorem old_triple_product (a b c : Fˣ) :
    threeEquiv F (product 1 2 (symbol ![a]) (symbol ![b, c])) =
      MilnorK.K3.symbol3 a b c := by
  rw [product_symbol, threeEquiv_symbol]
  rfl

/-- Pair insertion is through actual old K₂, with the chosen adjacent positions unchanged. -/
theorem actual_adjacent_insertion (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b c : Fˣ) :
    adjacentPairMap a i j hij (MilnorK.K2.symbol b c) =
      symbol (Function.update (Function.update a i b) j c) :=
  adjacentPairMap_symbol a i j hij b c

/-- Adjacent skew symmetry is available with arbitrary remaining coordinates. -/
theorem swap_adjacent (a : SymbolTuple F n) (i j : Fin n) (hij : i.val + 1 = j.val) :
    symbol a = -symbol (Function.update (Function.update a i (a j)) j (a i)) :=
  symbol_adjacent_skew a i j hij

/-- The correct diagonal formula uses `-1` rather than assuming alternation. -/
theorem adjacent_diagonal (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : a i = a j) :
    symbol a = symbol (Function.update a j (-1)) := symbol_adjacent_self a i j hij h

/-- A concrete fourth-degree identity checks insertion away from both endpoints. -/
theorem degree_four_middle_skew (a b c d : Fˣ) :
    symbol ![a, b, c, d] = -symbol ![a, c, b, d] := by
  have ht : Function.update (Function.update ![a, b, c, d] 1 c) 2 b = ![a, c, b, d] := by
    funext i
    fin_cases i <;> simp
  have h := symbol_adjacent_skew ![a, b, c, d] 1 2 rfl
  change symbol ![a, b, c, d] =
    -symbol (Function.update (Function.update ![a, b, c, d] 1 c) 2 b) at h
  rwa [ht] at h

/-- The diagonal identity specializes correctly in characteristic two. -/
theorem characteristic_two_diagonal (a : SymbolTuple (ZMod 2) n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : a i = a j) : symbol a = 0 := by
  rw [symbol_adjacent_self a i j hij h]
  have hneg : (-1 : (ZMod 2)ˣ) = 1 := by
    apply Units.ext
    decide
  rw [hneg, symbol_update_one]

variable {F} {E : Type v} [Field E]

/-- Product naturality holds across independently sized field universes. -/
theorem cross_universe_naturality (f : F →+* E) (x : K F m) (y : K F n) :
    map (m + n) f (product m n x y) = product m n (map m f x) (map n f y) :=
  map_product f x y

end AglibTest.GeneralMilnorProduct

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
    throwError "The general Milnor product audit requires legacy imports"
  let libraryPrefix := `MilnorK
  let consumerPrefix := `AglibTest.GeneralMilnorProduct
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
  logInfo m!"Audited {count} general Milnor product and consumer declarations, including private \
    helpers: only standard Lean logical foundations."
