/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.LowDegree
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit for the all-degree Milnor presentation

These tests exercise the actual quotient, arbitrary degrees and universes,
identity-axis and adjacent Steinberg relations, the unique extension property,
field functoriality, and the genuine degree-zero and degree-one equivalences.
The positive-characteristic test explicitly prevents any characteristic-zero
restriction from entering the foundational presentation.
-/

open MilnorK

namespace AglibTest.GeneralMilnorBasic

universe u v w

variable (F : Type u) [Field F] (n : ℕ)

/-- The group is literally the integer free-symbol quotient, in every degree. -/
theorem actual_quotient :
    K F n = (((Fin n → Fˣ) →₀ ℤ) ⧸ Submodule.span ℤ (relationGenerators F n)) := rfl

/-- Symbols are the classes of singleton generators with coefficient one. -/
theorem actual_symbol (a : SymbolTuple F n) :
    symbol a = (relationSpan F n).mkQ (Finsupp.single a 1) := rfl

/-- The presentation imposes multiplicativity at any specified coordinate. -/
theorem coordinate_additivity (a : SymbolTuple F n) (i : Fin n) (b c : Fˣ) :
    symbol (Function.update a i (b * c)) =
      symbol (Function.update a i b) + symbol (Function.update a i c) :=
  symbol_mul a i b c

/-- The actual quotient kills every adjacent Steinberg pair. -/
theorem adjacent_steinberg (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : (a i : F) + (a j : F) = 1) : symbol a = 0 :=
  steinberg a i j hij h

/-- Every identity axis vanishes in every positive degree. -/
theorem identity_axis (a : SymbolTuple F n) (i : Fin n) (h : a i = 1) : symbol a = 0 :=
  symbol_eq_zero_of_eq_one a i h

variable {A : Type v} [AddCommGroup A]

/-- The universal property is unique extension, with no extra field or norm hypotheses. -/
theorem unique_extension (s : SymbolTuple F n → A) (hs : IsSymbolMap s) :
    ∃! f : K F n →ₗ[ℤ] A, ∀ a, f (symbol a) = s a := existsUnique_lift s hs

variable {F} {E : Type v} {L : Type w} [Field E] [Field L]

/-- Field maps between independently sized universes act coordinatewise. -/
theorem cross_universe_field_map (f : F →+* E) (a : SymbolTuple F n) :
    map n f (symbol a) = symbol ((Units.map f.toMonoidHom) ∘ a) := map_symbol n f a

/-- Field composition is respected, including three independent universe levels. -/
theorem cross_universe_composition (f : F →+* E) (g : E →+* L) :
    map n (g.comp f) = (map n g).comp (map n f) := map_comp n f g

/-- Identity field maps induce identity maps on the actual groups. -/
theorem field_identity : map n (RingHom.id F) = LinearMap.id := map_id n

variable (F)

/-- The degree-zero symbol is the canonical generator of the integers. -/
theorem zeroth_normalization (a : SymbolTuple F 0) : zeroEquiv F (symbol a) = 1 :=
  zeroEquiv_symbol F a

/-- Degree zero is not accidentally collapsed by the relations. -/
theorem empty_symbol_ne_zero (a : SymbolTuple F 0) : symbol a ≠ 0 := by
  intro h
  have he := congrArg (zeroEquiv F) h
  simp at he

/-- The degree-one symbol has exactly the original multiplicative unit value. -/
theorem first_normalization (a : SymbolTuple F 1) :
    oneEquiv F (symbol a) = Additive.ofMul (a 0) := oneEquiv_symbol F a

/-- Degree-one vanishing is precisely the identity-unit condition. -/
theorem first_symbol_eq_zero_iff (a : SymbolTuple F 1) : symbol a = 0 ↔ a 0 = 1 := by
  constructor
  · intro h
    have he := congrArg (oneEquiv F) h
    simpa using he
  · exact symbol_eq_zero_of_eq_one a 0

/-- All-degree Milnor K-theory and its degree-zero normalization exist in characteristic two. -/
theorem characteristic_two_zero :
    zeroEquiv (ZMod 2) (symbol (F := ZMod 2) Fin.elim0) = 1 := by simp

/-- Low-degree naturality checks the field action against the explicit equivalences. -/
theorem zero_field_compatibility (f : F →+* E) (x : K F 0) :
    zeroEquiv E (map 0 f x) = zeroEquiv F x := zeroEquiv_map f x

/-- Degree one is compatible with the actual induced homomorphism of unit groups. -/
theorem one_field_compatibility (f : F →+* E) (x : K F 1) :
    oneEquiv E (map 1 f x) =
      Additive.ofMul (Units.map f.toMonoidHom (oneEquiv F x).toMul) := oneEquiv_map f x

end AglibTest.GeneralMilnorBasic

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
    throwError "The general Milnor audit requires legacy imports to include private helpers"
  let libraryPrefix := `MilnorK
  let consumerPrefix := `AglibTest.GeneralMilnorBasic
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
  logInfo m!"Audited {count} general Milnor and consumer declarations, including private helpers: \
    only standard Lean logical foundations."
