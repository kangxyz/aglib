/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K3.PolynomialNormSplit
import Lean.Util.CollectAxioms

/-!
# Original-group consumers and rejecting audit for split polynomial norms

The consumers retain the original K₂ presentation, coefficient inclusion,
root-evaluation equivalence, full finite factor set, and arbitrary entries in
both source-symbol coordinates. The audit includes private imported helpers
and rejects every assumption outside the standard Lean logical foundations.
-/

open Polynomial Polynomial.LocalResidue
open MilnorK.K2
open MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm

noncomputable section

namespace AglibTest.PolynomialNormSplit

variable {k L : Type*} [Field k] [Field L]

/-- The source is the original integer tensor quotient, without changed scalars. -/
theorem original_source (p : MonicIrreducible k) :
    MilnorK.K2.Group (AdjoinRoot p.val) =
      (TensorProduct ℤ (Additive (AdjoinRoot p.val)ˣ) (Additive (AdjoinRoot p.val)ˣ) ⧸
        steinbergSpan (AdjoinRoot p.val)) := rfl

/-- The target remains the actual target-field Milnor K₂ group. -/
theorem original_target :
    MilnorK.K2.Group L = (TensorProduct ℤ (Additive Lˣ) (Additive Lˣ) ⧸ steinbergSpan L) := rfl

/-- The inverse to branch evaluation is literally the original coefficient map. -/
theorem original_scalar_inverse (q : MonicIrreducible L) (hq : q.val.natDegree = 1) :
    (rootEvaluationEquiv q hq).symm.toRingHom = algebraMap L (AdjoinRoot q.val) :=
  rootEvaluationEquiv_symm_toRingHom q hq

/-- Evaluation on quotient classes is the usual polynomial evaluation. -/
theorem degree_one_evaluation (q : MonicIrreducible L) (hq : q.val.natDegree = 1)
    (f : L[X]) :
    (rootEvaluationEquiv q hq) (AdjoinRoot.mk q.val f) = f.eval (-q.val.coeff 0) :=
  rootEvaluation_mk q hq f

/-- The degree-one norm formula does not need a characteristic-zero assumption. -/
theorem actual_degree_one_norm (q : MonicIrreducible L) (hq : q.val.natDegree = 1)
    (z : MilnorK.K2.Group (AdjoinRoot q.val)) :
    polynomialNorm q z = MilnorK.K2.map (rootEvaluationEquiv q hq).toRingHom z :=
  LinearMap.congr_fun (polynomialNorm_eq_map_rootEvaluationEquiv q hq) z

/-- Every old coefficient class is fixed by the degree-one norm. -/
theorem actual_degree_one_retraction (q : MonicIrreducible L) (hq : q.val.natDegree = 1)
    (z : MilnorK.K2.Group L) :
    polynomialNorm q (MilnorK.K2.map (algebraMap L (AdjoinRoot q.val)) z) = z := by
  rw [polynomialNorm_map_constants, hq, Nat.cast_one, one_smul]

/-- Neither coordinate of a degree-one source symbol is restricted to constants. -/
theorem actual_degree_one_symbol (q : MonicIrreducible L) (hq : q.val.natDegree = 1)
    (a b : (AdjoinRoot q.val)ˣ) :
    polynomialNorm q (symbol a b) =
      symbol (Units.map (rootEvaluation q hq).toMonoidHom a)
        (Units.map (rootEvaluation q hq).toMonoidHom b) := by
  rw [polynomialNorm_eq_map_rootEvaluation q hq, MilnorK.K2.map_symbol]

/-- The existing full finite index contains exactly all monic irreducible factors. -/
theorem no_factor_is_discarded (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) :
    q ∈ placesAbove φ p ↔ q.val ∣ p.val.map φ := mem_placesAbove φ p q

/-- Splitting proves linearity for each original branch, with no extra input. -/
theorem every_original_branch_linear (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) :
    q.val.val.natDegree = 1 :=
  natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property

/-- Every embedding factors through the actual whole scalar algebra and quotient. -/
theorem literal_scalar_branch (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) :
    splitBranchMap φ p hp q =
      (rootEvaluation q.val
        (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property)).comp
          ((AdjoinRoot.divisorMap (p.val.map φ) q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).comp
              (AdjoinRoot.scalarMap φ p.val)) :=
  splitBranchMap_eq_eval_divisor_scalarMap φ p hp q

/-- The old scalar map, rather than an abstract replacement, is preserved. -/
theorem actual_scalar_map (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) (a : k) :
    splitBranchMap φ p hp q (algebraMap k (AdjoinRoot p.val) a) = φ a :=
  splitBranchMap_algebraMap φ p hp q a

/-- Each source polynomial is evaluated at the corresponding original root. -/
theorem actual_source_polynomial_evaluation (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) (f : k[X]) :
    splitBranchMap φ p hp q (AdjoinRoot.mk p.val f) = f.eval₂ φ (-q.val.val.coeff 0) :=
  splitBranchMap_mk φ p hp q f

/-- Distinct original factors do not produce repeated embeddings. -/
theorem original_branches_distinct (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) : Function.Injective (splitBranchMap φ p hp) :=
  splitBranchMap_injective_index φ p hp

open scoped Classical in
/-- The complete factor sum computes restriction of every original K₂ class. -/
theorem actual_split_norm [CharZero k] (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (z : MilnorK.K2.Group (AdjoinRoot p.val)) :
    MilnorK.K2.map φ (polynomialNorm p z) =
      ∑ q ∈ (placesAbove φ p).attach,
        MilnorK.K2.map (splitBranchMap φ p hp q) z :=
  polynomialNorm_restrict_of_splits φ p hp z

open scoped Classical in
/-- Equality is on actual integer-linear maps, without replacement groups. -/
theorem actual_split_integer_linear_maps [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits) :
    ((MilnorK.K2.map φ).comp (polynomialNorm p) :
        MilnorK.K2.Group (AdjoinRoot p.val) →ₗ[ℤ] MilnorK.K2.Group L) =
      ∑ q ∈ (placesAbove φ p).attach,
        MilnorK.K2.map (splitBranchMap φ p hp q) :=
  polynomialNorm_comp_restrict_of_splits φ p hp

open scoped Classical in
/-- Arbitrary units occur in both coordinates, including non-generating entries. -/
theorem actual_two_coordinate_symbol [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits)
    (a b : (AdjoinRoot p.val)ˣ) :
    MilnorK.K2.map φ (polynomialNorm p (symbol a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        symbol (Units.map (splitBranchMap φ p hp q).toMonoidHom a)
          (Units.map (splitBranchMap φ p hp q).toMonoidHom b) :=
  polynomialNorm_restrict_symbol_of_splits φ p hp a b

end AglibTest.PolynomialNormSplit

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
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
    throwError "The split polynomial norm audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`MilnorK.K2, `MilnorK.K3,
    `Motivic.Aglib.RingTheory.PolynomialLocalResidue,
    `Motivic.Aglib.RingTheory.PolynomialResidueBaseChange,
    `Motivic.Aglib.RingTheory.PolynomialPlaceContraction,
    `Motivic.Aglib.RingTheory.AdjoinRootScalarBranches,
    `Polynomial.LocalResidue,
    `Motivic.Aglib.FieldTheory.RatFuncInversion,
    `Motivic.Aglib.FieldTheory.RatFuncReverse,
    `Motivic.Aglib.FieldTheory.RatFuncCoefficientMap]
  let consumerPrefix := `AglibTest.PolynomialNormSplit
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
        throwError "Split polynomial norm declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂/K₃, literal scalar branches, and split polynomial \
    norm declarations, including private helpers: only standard Lean logical foundations."
