/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.ResidueChange
import Lean.Util.CollectAxioms

/-!
# Consumers and rejecting axiom audit of degree-three residue independence

The two actual nested-quotient maps are equal under elementary value and
unit-part change hypotheses. MotivicTest use arbitrary K₂ and K₃ classes, and retain
the normalization and repeated-uniformizer sign for the changed decomposition.
No residue equality, concrete DVR realization, or finite norm is an input.
-/

open MilnorK.K2 MilnorK.K3

namespace AglibTest.MilnorK3ResidueChange

variable {K k : Type*} [Field K] [Field k]

/-- The target is still the original degree-two tensor/Steinberg quotient. -/
theorem actual_original_target :
    MilnorK.K2.Group k = (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ steinbergSpan k) := rfl

/-- Source extensionality applies to the actual nested quotient and any additive target. -/
theorem maps_determined_by_actual_symbols {A : Type*} [AddCommGroup A]
    (f g : MilnorK.K3.Group K →ₗ[ℤ] A)
    (h : ∀ a b c : Kˣ, f (symbol3 a b c) = g (symbol3 a b c)) : f = g :=
  MilnorK.K3.linearMap_ext f g h

variable (d d' : DiscreteResidueData K k)
variable (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
variable (e : UnitsAdd k)
variable (hvalue : ∀ a, d'.value a = d.value a)
variable (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e)

include hd' e hvalue hunit

/-- Precursor invariance holds on every original K₂ class, not only on symbols. -/
theorem precursor_change_cancels (a : UnitsAdd K) (x : MilnorK.K2.Group K) :
    residue3Bilinear d' hd' a x = residue3Bilinear d hd a x := by
  rw [residue3Bilinear_eq_of_unitPart_change d d' hd hd' e hvalue hunit]

/-- The equality is an equality of actual quotient linear maps. -/
theorem actual_residue_maps_equal : residue3 d' hd' = residue3 d hd :=
  residue3_eq_of_unitPart_change d d' hd hd' e hvalue hunit

/-- Consequently every actual degree-three class has an invariant residue. -/
theorem actual_residue_classes_equal (x : MilnorK.K3.Group K) :
    residue3 d' hd' x = residue3 d hd x :=
  LinearMap.congr_fun (residue3_eq_of_unitPart_change d d' hd hd' e hvalue hunit) x

/-- The old residue has the literal normalization at the new uniformizer as well. -/
theorem changed_uniformizer_normalization (u v : Kˣ)
    (hu : d'.value (Additive.ofMul u) = 0) (hv : d'.value (Additive.ofMul v) = 0) :
    residue3 d hd (symbol3 d'.uniformizer u v) =
      symbol (d'.unitPart (Additive.ofMul u)).toMul
        (d'.unitPart (Additive.ofMul v)).toMul := by
  rw [← residue3_eq_of_unitPart_change d d' hd hd' e hvalue hunit]
  exact residue3_uniformizer_units d' hd' u v hu hv

/-- Independence preserves the nonzero-capable sign term at a repeated new uniformizer. -/
theorem changed_repeated_uniformizer_sign (u : Kˣ)
    (hu : d'.value (Additive.ofMul u) = 0) :
    residue3 d hd (symbol3 d'.uniformizer d'.uniformizer u) =
      symbolBilinear k (residueSign k) (d'.unitPart (Additive.ofMul u)) := by
  rw [← residue3_eq_of_unitPart_change d d' hd hd' e hvalue hunit]
  exact residue3_uniformizer_uniformizer_unit d' hd' u hu

end AglibTest.MilnorK3ResidueChange

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
    throwError "The Milnor K₃ change audit requires legacy imports to include private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3]
  let consumerPrefix := `AglibTest.MilnorK3ResidueChange
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
        throwError "Milnor K₃ change audit declaration {name} is missing from \
          the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} Milnor K₂/K₃ and residue-change consumer declarations, \
    including private helpers: only standard Lean logical foundations."
