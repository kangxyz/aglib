/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K2.Basic
import Aglib.KTheory.MilnorK.K2.Map
import Aglib.KTheory.MilnorK.K2.Symbols
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit of the original Milnor K₂ construction

These tests exercise the exact tensor quotient, its original unit symbols,
Steinberg relation, field functoriality, and both universal-property interfaces.
Legacy imports intentionally expose private implementation dependencies to the
exhaustive three-module axiom audit below. No norm, reciprocity, or motivic
comparison assumption is introduced.
-/

open MilnorK.K2

namespace AglibTest.MilnorK2

variable (K : Type*) [Field K]

/-- The imported group remains the original integer tensor quotient. -/
theorem actual_tensor_quotient :
    MilnorK.K2.Group K = (TensorProduct ℤ (Additive Kˣ) (Additive Kˣ) ⧸
      Submodule.span ℤ (steinbergGenerators K)) := rfl

/-- Its actual symbols are the quotient classes of pure unit tensors. -/
theorem actual_symbol (a b : Kˣ) :
    symbol a b = (steinbergSpan K).mkQ
      (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)) := rfl

/-- Multiplication of units is additive in the first argument. -/
theorem multiplicative_left (a b c : Kˣ) :
    symbol (a * b) c = symbol a c + symbol b c := symbol_mul_left a b c

/-- Multiplication of units is additive in the second argument. -/
theorem multiplicative_right (a b c : Kˣ) :
    symbol a (b * c) = symbol a b + symbol a c := symbol_mul_right a b c

/-- The symbol of a multiplicative identity vanishes in each position. -/
theorem identity_entries (a : Kˣ) : symbol 1 a = 0 ∧ symbol a 1 = 0 :=
  ⟨symbol_one_left a, symbol_one_right a⟩

/-- Inverses act by additive negation in each position. -/
theorem inverse_entries (a b : Kˣ) :
    symbol a⁻¹ b = -symbol a b ∧ symbol a b⁻¹ = -symbol a b :=
  ⟨symbol_inv_left a b, symbol_inv_right a b⟩

/-- The original Steinberg relation is proved in that quotient. -/
theorem actual_steinberg (a b : Kˣ) (hab : (a : K) + (b : K) = 1) :
    symbol a b = 0 := steinberg a b hab

/-- The standard one-minus-unit form uses the actual constructed unit. -/
theorem actual_one_sub (a : Kˣ) (ha : a ≠ 1) :
    symbol a (oneSub a ha) = 0 := symbol_oneSub a ha

/-- Anticommutativity is derived from the presentation. -/
theorem actual_skew (a b : Kˣ) : symbol a b = -symbol b a := symbol_skew a b

variable {K} {L M : Type*} [Field L] [Field M]

/-- The original field map takes actual unit symbols to actual unit symbols. -/
theorem field_map_symbol (f : K →+* L) (a b : Kˣ) :
    mapAdd f (symbol a b) =
      symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  mapAdd_symbol f a b

/-- The additive field maps preserve identities with no extra hypothesis. -/
theorem field_map_identity : mapAdd (RingHom.id K) = AddMonoidHom.id (MilnorK.K2.Group K) :=
  mapAdd_id

/-- The additive field maps preserve composition with no extra hypothesis. -/
theorem field_map_composition (f : K →+* L) (g : L →+* M) :
    mapAdd (g.comp f) = (mapAdd g).comp (mapAdd f) := mapAdd_comp f g

variable {A : Type*} [AddCommGroup A]

/-- A bilinear Steinberg function has exactly one map from the tensor quotient. -/
theorem linear_universal_property (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) :
    ∃! f : MilnorK.K2.Group K →ₗ[ℤ] A, ∀ a c : Kˣ,
      f (symbol a c) = b (Additive.ofMul a) (Additive.ofMul c) :=
  existsUnique_lift b hb

/-- The convenience interface still evaluates through the original quotient. -/
theorem additive_lift_symbol (s : SymbolMap (K := K) (A := A)) (a b : Kˣ) :
    liftSymbols s (symbol a b) = s.toFun a b := liftSymbols_symbol s a b

/-- Its additive universal property also retains uniqueness. -/
theorem additive_universal_property (s : SymbolMap (K := K) (A := A)) :
    ∃! f : MilnorK.K2.Group K →+ A, ∀ a b : Kˣ, f (symbol a b) = s.toFun a b := by
  refine ⟨liftSymbols s, liftSymbols_symbol s, ?_⟩
  intro f hf
  exact liftSymbols_unique s f hf

/-- Taking the genuine symbol function reconstructs the identity map. -/
theorem self_lift_identity :
    liftSymbols ({
      toFun := symbol
      mul_left := symbol_mul_left
      mul_right := symbol_mul_right
      steinberg := steinberg
    } : SymbolMap (K := K) (A := MilnorK.K2.Group K)) = AddMonoidHom.id (MilnorK.K2.Group K) := by
  apply symbolHom_ext
  intro a b
  rfl

end AglibTest.MilnorK2

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
    throwError "The Milnor K₂ audit requires legacy imports to include private helpers"
  let libraryPrefix := `MilnorK.K2
  let consumerPrefix := `AglibTest.MilnorK2
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || libraryPrefix.isPrefixOf name || consumerPrefix.isPrefixOf name
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
      if libraryOrigin || libraryPrefix.isPrefixOf name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "Milnor K₂ audit declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂ and consumer declarations, including private \
    helpers: only standard Lean logical foundations."
