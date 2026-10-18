/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K2.Specialization
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit of original Milnor K₂ residues

These tests retain the original explicit normalized valuation data and
zero-valuation residue compatibility. They exercise the constructed tame and
specialization maps, their sign conventions, change formula, actual tame kernel,
and constant retraction. Legacy imports intentionally expose private helpers
for the exhaustive five-module audit. No concrete DVR, Quillen comparison,
finite-extension norm, or reciprocity assertion is assumed or claimed.
-/

open MilnorK.K2

namespace AglibTest.MilnorK2Residue

variable {K k : Type*} [Field K] [Field k]

/-- The tame map is the actual descent of the proved bilinear formula. -/
theorem actual_tame_descent (d : DiscreteResidueData K k) :
    tame d = lift (tameBilinear d) (fun a b hab => rawTame_steinberg d a b hab) := rfl

/-- The signed additive formula keeps the sign in additive residue units. -/
theorem actual_tame_formula (d : DiscreteResidueData K k) (a b : Kˣ) :
    tame d (symbol a b) =
      (d.value (Additive.ofMul a) * d.value (Additive.ofMul b)) • residueSign k +
        d.value (Additive.ofMul b) • d.unitPart (Additive.ofMul a) -
        d.value (Additive.ofMul a) • d.unitPart (Additive.ofMul b) := rfl

/-- The original raw formula kills Steinberg pairs without a tame-map premise. -/
theorem actual_tame_steinberg (d : DiscreteResidueData K k) (a b : Kˣ)
    (hab : (a : K) + (b : K) = 1) :
    rawTame d (Additive.ofMul a) (Additive.ofMul b) = 0 :=
  rawTame_steinberg d a b hab

/-- The multiplicative residue formula preserves the original sign convention. -/
theorem multiplicative_tame_formula (d : DiscreteResidueData K k) (a b : Kˣ) :
    tameValue d (symbol a b) =
      (-1 : kˣ) ^ (d.value (Additive.ofMul a) * d.value (Additive.ofMul b)) *
        (d.unitPart (Additive.ofMul a)).toMul ^ d.value (Additive.ofMul b) /
        (d.unitPart (Additive.ofMul b)).toMul ^ d.value (Additive.ofMul a) :=
  tameValue_symbol d a b

/-- Addition in K₂ becomes multiplication in residue units. -/
theorem multiplicative_tame_addition (d : DiscreteResidueData K k) (x y : MilnorK.K2.Group K) :
    tameValue d (x + y) = tameValue d x * tameValue d y := tameValue_add d x y

/-- Two valuation units have trivial tame residue. -/
theorem tame_two_units (d : DiscreteResidueData K k) (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    tame d (symbol u v) = 0 := tame_units d u v hu hv

/-- The original degree-two normalization places the uniformizer last. -/
theorem tame_uniformizer_last (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol u d.uniformizer) = d.unitPart (Additive.ofMul u) :=
  tame_unit_uniformizer d u hu

/-- Moving the uniformizer to the first position changes the additive sign. -/
theorem tame_uniformizer_first (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol d.uniformizer u) = -d.unitPart (Additive.ofMul u) :=
  tame_uniformizer_unit d u hu

/-- Two uniformizers give the residue of minus one, not a forced zero. -/
theorem tame_uniformizer_diagonal (d : DiscreteResidueData K k) :
    tame d (symbol d.uniformizer d.uniformizer) = residueSign k := by
  simp [tame_symbol, rawTame, d.value_uniformizer, d.unitPart_uniformizer]

/-- The residue sign has additive order dividing two. -/
theorem sign_order_two : residueSign k + residueSign k = 0 := residueSign_add_self

/-- Pairing the residue sign with any unit gives a class killed by two. -/
theorem sign_pair_order_two (u : UnitsAdd k) :
    symbolBilinear k (residueSign k) u + symbolBilinear k (residueSign k) u = 0 := by
  have h := congrArg ((symbolBilinear k).flip u) (residueSign_add_self (k := k))
  simpa only [map_add, map_zero, LinearMap.flip_apply] using h

/-- Residue-characteristic-primary torsion has multiplicative tame value one. -/
theorem tame_primary_torsion (d : DiscreteResidueData K k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (x : MilnorK.K2.Group K)
    (hx : (p ^ r) • x = 0) : tameValue d x = 1 :=
  tameValue_primePower_torsion d p r x hx

/-- Specialization is the actual quotient lift after proving Steinberg. -/
theorem actual_specialization_descent (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) :
    specialize d hd = lift (specializationBilinear d)
      (fun a b hab => specialization_steinberg d hd a b hab) := rfl

/-- Specialization takes every symbol to the two original residue unit parts. -/
theorem actual_specialization_formula (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b : Kˣ) :
    specialize d hd (symbol a b) =
      symbol (d.unitPart (Additive.ofMul a)).toMul (d.unitPart (Additive.ofMul b)).toMul :=
  specialize_symbol d hd a b

/-- The chosen uniformizer specializes to a trivial first symbol entry. -/
theorem specialization_uniformizer_first (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (u : Kˣ) :
    specialize d hd (symbol d.uniformizer u) = 0 := by
  simp [specialize_symbol, d.unitPart_uniformizer]

/-- The chosen uniformizer specializes to a trivial second symbol entry. -/
theorem specialization_uniformizer_last (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (u : Kˣ) :
    specialize d hd (symbol u d.uniformizer) = 0 := by
  simp [specialize_symbol, d.unitPart_uniformizer]

/-- Changing compatible unit parts leaves the constructed tame map invariant. -/
theorem tame_change_invariance (d d' : DiscreteResidueData K k) (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) : tame d' = tame d :=
  tame_eq_of_unitPart_change d d' e hvalue hunit

/-- The actual tame kernels coincide under the same elementary change data. -/
theorem actual_kernel_change (d d' : DiscreteResidueData K k) (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    (tame d').ker = (tame d).ker := tame_kernel_eq_of_unitPart_change d d' e hvalue hunit

/-- The full-group specialization change is a proved tame correction. -/
theorem actual_specialization_change (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    specialize d' hd' = specialize d hd - (residueCorrection e).comp (tame d) :=
  specialize_change d d' hd hd' e hunit

/-- Skew symmetry gives the original manuscript's equivalent correction order. -/
theorem specialization_change_order (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) (x : MilnorK.K2.Group K) :
    specialize d' hd' x - specialize d hd x = symbolBilinear k e (tame d x) :=
  specialize_change_source_convention d d' hd hd' e hunit x

/-- The change vanishes on the actual kernel, with no substitute kernel interface. -/
theorem actual_unramified_invariance (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    (specialize d' hd').comp (tame d).ker.subtype = unramifiedSpecialize d hd :=
  specialize_eq_on_tame_kernel d d' hd hd' e hunit

/-- Constants with the stated residue unit parts admit a genuine retraction. -/
theorem constants_retraction (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    (specialize d hd).comp (map i) = LinearMap.id := specialize_map_constants d hd i hunit

/-- Constant injectivity is a consequence rather than an extra hypothesis. -/
theorem constants_injective (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    Function.Injective (map i) := map_constants_injective d hd i hunit

/-- The retraction persists after restricting constants to the actual tame kernel. -/
theorem unramified_retraction (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hvalue : ∀ a : kˣ, d.value (unitsLinear i (Additive.ofMul a)) = 0)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    (unramifiedSpecialize d hd).comp (unramifiedConstants d i hvalue) = LinearMap.id :=
  unramified_constants_retraction d hd i hvalue hunit

end AglibTest.MilnorK2Residue

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
    throwError "The Milnor K₂ residue audit requires legacy imports to include private helpers"
  let libraryPrefix := `MilnorK.K2
  let consumerPrefix := `AglibTest.MilnorK2Residue
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
        throwError "Milnor K₂ residue audit declaration {name} is missing \
          from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂ and residue-consumer declarations, including \
    private helpers: only standard Lean logical foundations."
