/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialNormBaseChange
import Lean.Util.CollectAxioms

/-!
# Original-group consumers and rejecting audit for polynomial norm base change

The consumers retain arbitrary coefficient-field maps, explicit characteristic
zero, actual finite factor sets, literal quotient-field homomorphisms, and the
original integer-linear Milnor K₂ groups. No compatibility data are inputs.
-/

open Polynomial Polynomial.LocalResidue
open MilnorK.K2 MilnorK.K3
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm

noncomputable section

namespace AglibTest.MilnorK3PolynomialNormBaseChange

variable {k L : Type*} [Field k] [Field L]

/-- The source is literally the original integer tensor/Steinberg quotient. -/
theorem original_source (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) =
      (TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val)) := rfl

/-- The target is literally the original target-field Milnor K₂ group. -/
theorem original_target :
    MilnorK.K2.Group L = (TensorProduct ℤ (Additive Lˣ) (Additive Lˣ) ⧸ steinbergSpan L) := rfl

/-- The indexing finite set consists exactly of the genuine polynomial factors. -/
theorem genuine_finite_factor_set (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) :
    q ∈ placesAbove φ p ↔ q.val ∣ p.val.map φ := mem_placesAbove φ p q

/-- The infinity proof supplies actual total norm compatibility on K₃ residues. -/
theorem actual_total_norm_restriction [CharZero k]
    (φ : k →+* L) (x : MilnorK.K3.Group (RatFunc k)) :
    MilnorK.K2.map φ (totalNorm (totalResidue x)) =
      totalNorm (totalResidue (MilnorK.K3.map (fractionMap φ) x)) :=
  totalNorm_restrict_totalResidue φ x

open scoped Classical in
/-- Every class of the original source K₂ obeys the actual finite norm formula;
no algebraicity or finite-dimensionality is assumed for the coefficient map. -/
theorem original_finite_norm_formula [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (z : MilnorK.K2.Group (AdjoinRoot p.val)) :
    MilnorK.K2.map φ (polynomialNorm p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm q.val
          (MilnorK.K2.map (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)) z) :=
  polynomialNorm_restrict φ p z

open scoped Classical in
/-- The equality is between original integer-linear maps, rather than maps on
replacement groups or groups with enlarged scalars. -/
theorem original_integer_linear_formula [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) :
    ((MilnorK.K2.map φ).comp (polynomialNorm p) :
        MilnorK.K2.Group (AdjoinRoot p.val) →ₗ[ℤ] MilnorK.K2.Group L) =
      ∑ q ∈ (placesAbove φ p).attach,
        (polynomialNorm q.val).comp
          (MilnorK.K2.map (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) :=
  polynomialNorm_comp_restrict φ p

open scoped Classical in
/-- The same theorem computes actual source symbols without any assumed norm
or residue compatibility interface. -/
theorem original_symbol_formula [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (a b : (AdjoinRoot p.val)ˣ) :
    MilnorK.K2.map φ (polynomialNorm p (symbol a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm q.val
          (symbol
            (Units.map (adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom a)
            (Units.map (adjoinRootMap φ p.val q.val.val
              ((mem_placesAbove φ p q.val).mp q.property)).toMonoidHom b)) := by
  simpa only [MilnorK.K2.map_symbol] using
    polynomialNorm_restrict φ p (symbol a b)

end AglibTest.MilnorK3PolynomialNormBaseChange

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialResidueBaseChange]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The polynomial norm base-change audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue,
    `Motivic.Aglib.RingTheory.PolynomialResidueBaseChange,
    `Motivic.Aglib.RingTheory.PolynomialPlaceContraction,
    `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion,
    `Motivic.Aglib.FieldTheory.RatFuncReverse,
    `Motivic.Aglib.FieldTheory.RatFuncCoefficientMap]
  let consumerPrefix := `AglibTest.MilnorK3PolynomialNormBaseChange
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
        throwError "Polynomial norm base-change declaration {name} \
          is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂/K₃, polynomial local residue, coefficient-map, \
    finite-place contraction, support, and polynomial norm base-change declarations, \
    including private helpers: only standard Lean logical foundations."
