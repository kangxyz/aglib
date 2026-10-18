/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.HenselianUniformizerNormalization
import Lean.Util.CollectAxioms

/-! Direct consumers preserve the literal local map, the actual residue-one
root and the normalized uniformizer equation. Invertibility of the exponent
is explicit except where residue characteristic zero genuinely supplies it. -/

open IsLocalRing

namespace AglibTest.HenselianUniformizerNormalization

variable {R S : Type*} [CommRing R] [IsLocalRing R]
  [CommRing S] [HenselianLocalRing S] (j : R →+* S) [IsLocalHom j]
  (hj : Function.Surjective (ResidueField.map j))

include hj

/-- The lift is a genuine base-ring unit, not merely a residue-field scalar. -/
theorem unit_lift (u : Sˣ) :
    ∃ a : Rˣ, residue S (j (a : R)) = residue S (u : S) :=
  IsLocalRing.exists_unit_residue_lift j hj u

/-- No characteristic assumption is needed for an explicitly invertible exponent. -/
theorem principal_root_factorization (e : ℕ) (he : 0 < e)
    (heunit : IsUnit (e : S)) (u : Sˣ) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Units.map j.toMonoidHom a * v ^ e = u :=
  IsLocalRing.exists_base_unit_mul_principal_pow j hj e he heunit u

/-- The exponent-one edge case retains the actual residue-one adjustment. -/
theorem exponent_one {π : R} {ϖ : S} (hϖ : Irreducible ϖ)
    (u : Sˣ) (hπ : j π = (u : S) * ϖ) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧ j π = j (a : R) * ((v : S) * ϖ) := by
  simpa only [pow_one] using IsLocalRing.exists_principal_adjusted_uniformizer
    j hj hϖ u 1 (by decide) (by simp)
    (by simpa only [pow_one] using hπ)

/-- Residue characteristic zero supplies invertibility, rather than being
silently inferred from characteristic zero of a fraction field. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)]
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ) (u : Sˣ) (e : ℕ) (he : 0 < e)
    (hπ : j π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧ j π = j (a : R) * ((v : S) * ϖ) ^ e :=
  IsLocalRing.exists_principal_adjusted_uniformizer j hj hϖ u e he
    (HenselianLocalRing.PrincipalRoots.isUnit_natCast_of_residue_charZero e he) hπ

omit hj in
/-- The degree-one corollary uses the original residue algebra structure. -/
theorem actual_residue_degree_one [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1)
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ) (u : Sˣ) (e : ℕ) (he : 0 < e)
    (heunit : IsUnit (e : S)) (hπ : algebraMap R S π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧
      algebraMap R S π = algebraMap R S (a : R) * ((v : S) * ϖ) ^ e :=
  HenselianLocalRing.exists_principal_adjusted_uniformizer_of_residue_finrank_one
    R S hf hϖ u e he heunit hπ

end AglibTest.HenselianUniformizerNormalization

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.HenselianPrincipalRoots,
    `Aglib.RingTheory.HenselianUniformizerNormalization]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let native := #[`IsLocalRing.exists_unit_residue_lift,
    `IsLocalRing.exists_base_unit_mul_principal_pow,
    `IsLocalRing.exists_principal_adjusted_uniformizer,
    `HenselianLocalRing.exists_principal_adjusted_uniformizer_of_residue_finrank_one]
  let selectedDeclaration (name : Name) := native.contains name ||
    (`AglibTest.HenselianUniformizerNormalization).isPrefixOf name
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
  logInfo m!"Checked {names.size} normalization declarations: standard axioms only."
