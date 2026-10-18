/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.BaseChange
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of actual all-degree polynomial norm base change. The
finite sum uses all actual target factors and literal quotient-field maps.
Degree zero, map equality and the existing degree law remain visible. -/

open Polynomial Polynomial.LocalResidue
open MilnorK MilnorK.PolynomialResidue MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormBaseChange

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

open scoped Classical in
/-- The branch sum applies to an arbitrary class of the actual quotient. -/
theorem arbitrary_class [CharZero k] (n : ℕ) (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) n) :
    map n φ (polynomialNorm n p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm n q.val
          (map n (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)) z) :=
  polynomialNorm_restrict φ n p z

open scoped Classical in
/-- The formula also holds as equality of the actual linear maps. -/
theorem actual_map_square [CharZero k] (n : ℕ) (p : MonicIrreducible k) :
    (map n φ).comp (polynomialNorm n p) =
      ∑ q ∈ (placesAbove φ p).attach,
        (polynomialNorm n q.val).comp
          (map n (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property))) :=
  polynomialNorm_comp_restrict φ n p

open scoped Classical in
/-- Degree zero is included with its original quotient groups. -/
theorem empty_degree [CharZero k] (p : MonicIrreducible k)
    (z : K (AdjoinRoot p.val) 0) :
    map 0 φ (polynomialNorm 0 p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        polynomialNorm 0 q.val
          (map 0 (adjoinRootMap φ p.val q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)) z) :=
  polynomialNorm_restrict φ 0 p z

open scoped Classical in
/-- Summing the actual branches is consistent with the already proved
restriction-then-norm degree law, for all base-field classes and degrees. -/
theorem base_class_degree [CharZero k] (n : ℕ) (p : MonicIrreducible k) (x : K k n) :
    (∑ q ∈ (placesAbove φ p).attach,
      polynomialNorm n q.val
        (map n (adjoinRootMap φ p.val q.val.val
          ((mem_placesAbove φ p q.val).mp q.property))
          (map n (algebraMap k (AdjoinRoot p.val)) x))) =
        (p.val.natDegree : ℤ) • map n φ x := by
  rw [← polynomialNorm_restrict, polynomialNorm_map_constants, map_smul]

/-- Total norms of actual rational residue vectors are natural without a
characteristic-zero premise; this concrete source has characteristic two. -/
theorem total_norm_characteristic_two (ψ : ZMod 2 →+* L) (n : ℕ)
    (x : K (RatFunc (ZMod 2)) (n + 1)) :
    map n ψ (totalNorm n (totalResidue n x)) =
      totalNorm n (totalResidue n (map (n + 1) (fractionMap ψ) x)) :=
  totalNorm_restrict_totalResidue ψ n x

end AglibTest.GeneralMilnorPolynomialNormBaseChange

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
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK,
    `AglibTest.GeneralMilnorPolynomialNormBaseChange]
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
  logInfo m!"Checked {names.size} polynomial norm base-change and general Milnor declarations: \
    standard axioms only."
