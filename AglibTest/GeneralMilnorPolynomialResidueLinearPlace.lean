/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearPlace
import Lean.Util.CollectAxioms

/-! Direct consumer recovering the original finite residue after linearization. -/

namespace AglibTest.GeneralMilnorPolynomialResidueLinearPlace

open MilnorK Polynomial Polynomial.LocalResidue
open MilnorK.PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]
variable (p : k[X]) [Fact (Irreducible p)]

local instance (a : AdjoinRoot p) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- Equality of actual original maps, not just evaluation on symbolic generators. -/
theorem original_residue_map (n : ℕ) :
    residueAt p n =
      (map n (linearRootEquiv (AdjoinRoot.root p)).toRingHom).comp
        ((residueAt (X - C (AdjoinRoot.root p)) n).comp
          (map (n + 1) (fractionMap (algebraMap k (AdjoinRoot p))))) := by
  apply LinearMap.ext
  intro x
  exact residueAt_eq_linearPlace p n x

end AglibTest.GeneralMilnorPolynomialResidueLinearPlace

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialResidueBaseChange]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK,
    `AglibTest.GeneralMilnorPolynomialResidueLinearPlace]
  let selectedDeclaration (name : Name) := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} linear finite-place and Milnor declarations: \
    standard axioms only."
