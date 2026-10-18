/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.DVRRamificationDegree
import Lean.Util.CollectAxioms

/-! Direct actual-data consumers of the ramification-times-residue degree
formula, including the two prime-degree branches and the nonzero exponent. -/

open IsLocalRing

namespace AglibTest.DVRRamificationDegree

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F] [PerfectField F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)

include F E hπ hϖ he

/-- The literal exponent and actual residue degree give the actual field degree. -/
theorem actual_degree :
    Module.finrank F E = e * Module.finrank (ResidueField R) (ResidueField S) :=
  IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u e he

/-- Finite field extensions are nonzero, so the supplied exponent must be positive. -/
theorem exponent_positive : 0 < e := by
  have hd := actual_degree R S F E hπ hϖ u e he
  have hn := Module.finrank_pos (R := F) (M := E)
  rw [hd] at hn
  apply Nat.pos_of_ne_zero
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hn

/-- Prime degree gives exactly the two actual alternatives. -/
theorem prime_dichotomy (hp : Nat.Prime (Module.finrank F E)) :
    e = 1 ∨ Module.finrank (ResidueField R) (ResidueField S) = 1 :=
  IsDiscreteValuationRing.ramification_eq_one_or_residue_finrank_eq_one
    R S F E hπ hϖ u e he hp

/-- In the residue-degree-one branch the literal exponent is the field degree. -/
theorem residue_degree_one
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1) :
    Module.finrank F E = e := by
  simpa only [hf, mul_one] using actual_degree R S F E hπ hϖ u e he

/-- In the exponent-one branch the residue degree is the field degree. -/
theorem exponent_one (he1 : e = 1) :
    Module.finrank F E = Module.finrank (ResidueField R) (ResidueField S) := by
  simpa only [he1, one_mul] using actual_degree R S F E hπ hϖ u e he

end AglibTest.DVRRamificationDegree

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.DVRNormValuation,
    `Aglib.RingTheory.DVRRamificationDegree]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let native := #[`IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank,
    `IsDiscreteValuationRing.ramification_eq_one_or_residue_finrank_eq_one]
  let selectedDeclaration (name : Name) := native.contains name ||
    (`AglibTest.DVRRamificationDegree).isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for name in native do names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual ramification-degree declarations: standard axioms only."
