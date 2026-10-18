/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.Restriction
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of all-degree coefficient restriction. Finite places
retain their actual divisibility and unramified hypotheses; infinity is
tested without characteristic-zero assumptions, also at a concrete prime
characteristic. Legacy imports support inspection of every proof body. -/

open Polynomial Polynomial.LocalResidue
open MilnorK

namespace AglibTest.GeneralMilnorPolynomialResidueRestriction

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

/-- Every actual finite factor has the all-degree residue square in
characteristic zero, on arbitrary quotient classes. -/
theorem finite_factor [CharZero k] (p : k[X]) (q : L[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    PolynomialResidue.residueAt q n (map (n + 1) (fractionMap φ) x) =
      map n (adjoinRootMap φ p q hq) (PolynomialResidue.residueAt p n x) :=
  PolynomialResidue.residueAt_restrict φ p q hq n x

/-- The map uses the canonical DVR residues and literal quotient-field
identifications, not a new polynomial-symbol residue. -/
theorem actual_dvr_square [CharZero k] (p : k[X]) (q : L[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)
    (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    map n (residueEquiv q).toRingHom
        (DVR.residue (Ring q) (RatFunc L) n (map (n + 1) (fractionMap φ) x)) =
      map n (adjoinRootMap φ p q hq)
        (map n (residueEquiv p).toRingHom (DVR.residue (Ring p) (RatFunc k) n x)) := by
  have h := PolynomialResidue.residueAt_restrict φ p q hq n x
  simpa only [PolynomialResidue.residueAt_eq_dvr, LinearMap.comp_apply] using h

section Variable

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Irreducible (X : L[X])) := ⟨irreducible_X⟩

/-- At `X` the mapped uniformizer is actually irreducible, in every
characteristic, so this finite square needs no characteristic-zero instance. -/
theorem variable_place (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    PolynomialResidue.residueAt X n (map (n + 1) (fractionMap φ) x) =
      map n (adjoinRootMap φ X X (by simp)) (PolynomialResidue.residueAt X n x) := by
  apply PolynomialResidue.residueAt_restrict_of_unramified
  simpa only [localRingMap_polynomial, Polynomial.map_X] using
    (irreducible_polynomial (X : L[X]))

end Variable

/-- Infinity restriction allows every quotient class and every residue degree. -/
theorem infinity_arbitrary_characteristic (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    InfinityResidue.residue L n (map (n + 1) (fractionMap φ) x) =
      map n φ (InfinityResidue.residue k n x) :=
  InfinityResidue.residue_restrict φ n x

/-- Last-slot inverse-variable normalization survives coefficient extension,
including the empty prefix in degree one. -/
theorem infinity_uniformizer_normalization (n : ℕ) (a : SymbolTuple k n) :
    InfinityResidue.residue L n
        (map (n + 1) (fractionMap φ)
          (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a)
            (InfinityResidue.variableUnit k)⁻¹))) =
      symbol (Units.map φ.toMonoidHom ∘ a) := by
  rw [InfinityResidue.residue_restrict, InfinityResidue.residue_inv_variable, map_symbol]

/-- The concrete characteristic-two source is admitted by the full infinity
theorem; no separability or characteristic-zero premise is introduced. -/
theorem infinity_characteristic_two (ψ : ZMod 2 →+* L) (n : ℕ)
    (x : K (RatFunc (ZMod 2)) (n + 1)) :
    InfinityResidue.residue L n (map (n + 1) (fractionMap ψ) x) =
      map n ψ (InfinityResidue.residue (ZMod 2) n x) :=
  InfinityResidue.residue_restrict ψ n x

end AglibTest.GeneralMilnorPolynomialResidueRestriction

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
    `AglibTest.GeneralMilnorPolynomialResidueRestriction]
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
  logInfo m!"Checked {names.size} polynomial restriction and general Milnor declarations: \
    standard axioms only."
