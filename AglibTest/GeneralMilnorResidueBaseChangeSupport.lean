/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.BaseChangeSupport
import Lean.Util.CollectAxioms

/-! Direct consumers of zero-contraction vanishing and full finite-factor
support after coefficient restriction, with the original dependent residues. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue

namespace AglibTest.GeneralMilnorResidueBaseChangeSupport

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

/-- Zero-contraction vanishing does not need characteristic zero. -/
theorem zero_contraction (q : L[X]) [Fact (Irreducible q)]
    (hq : ∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    residueAt q n (map (n + 1) (fractionMap φ) x) = 0 :=
  residueAt_restrict_zero_of_no_polynomial_divisor φ q hq n x

/-- Each arbitrary rational unit has an actual local-unit representative after
restriction, even if its source numerator or denominator has high degree. -/
theorem actual_local_unit (q : L[X]) [Fact (Irreducible q)]
    (hq : ∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ) (a : (RatFunc k)ˣ) :
    ∃ u : (Ring q)ˣ, MilnorK.K2.DVR.fieldUnits (Ring q) (RatFunc L) u =
      Units.map (fractionMap φ).toMonoidHom a :=
  exists_localUnit_restrict_of_no_polynomial_divisor φ q hq a

variable [CharZero k] [DecidableEq (MonicIrreducible k)]

/-- Every coordinate above the chosen place is its literal quotient-field map. -/
theorem factor_coordinate (n : ℕ) (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) n) (x : K (RatFunc k) (n + 1))
    (hx : totalResidue n x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : q.val ∣ p.val.map φ) :
    totalResidue n (map (n + 1) (fractionMap φ) x) q =
      map n (adjoinRootMap φ p.val q.val hq) z :=
  totalResidue_restrict_single_of_dvd φ n p z x hx q hq

/-- Every coordinate outside the factor set vanishes. -/
theorem outside_factor_coordinate (n : ℕ) (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) n) (x : K (RatFunc k) (n + 1))
    (hx : totalResidue n x = DFinsupp.single p z) (q : MonicIrreducible L)
    (hq : ¬q.val ∣ p.val.map φ) :
    totalResidue n (map (n + 1) (fractionMap φ) x) q = 0 :=
  totalResidue_restrict_single_of_not_dvd φ n p z x hx q hq

open scoped Classical in
/-- The dependent support, rather than only individual tested symbols, is bounded. -/
theorem full_dependent_support (n : ℕ) (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) n) (x : K (RatFunc k) (n + 1))
    (hx : totalResidue n x = DFinsupp.single p z) :
    (totalResidue n (map (n + 1) (fractionMap φ) x)).support ⊆ placesAbove φ p :=
  totalResidue_restrict_single_support_subset φ n p z x hx

end AglibTest.GeneralMilnorResidueBaseChangeSupport

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
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
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK,
    `AglibTest.GeneralMilnorResidueBaseChangeSupport]
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
  logInfo m!"Checked {names.size} residue base-change support and general Milnor declarations: \
    standard axioms only."
