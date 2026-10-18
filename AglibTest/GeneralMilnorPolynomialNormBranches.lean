/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Norm.Polynomial.Branches
import Lean.Util.CollectAxioms

/-! Actual branch reindexing, literal field-map commutation and strict degree
reduction for the root-field induction in the general norm comparison. -/

open Polynomial AdjoinRoot
open MilnorK.PolynomialNorm

namespace AglibTest.GeneralMilnorPolynomialNormBranches

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- Both directions retain every branch, including nonsplit branches. -/
theorem branch_roundtrip (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (r : IrreducibleBranch p) :
    (polynomialBranchEquiv p q hp hq e).symm
      (polynomialBranchEquiv p q hp hq e r) = r :=
  (polynomialBranchEquiv p q hp hq e).symm_apply_apply r

/-- The result is an equality of the original field homomorphisms, not only
an equality on roots or selected Milnor symbols. -/
theorem original_map_square (p q : k[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)]
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (r : IrreducibleBranch (p.map (algebraMap k L))) :
    let hp := Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero
    let hq := Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero
    let E := coefficientEquiv (L := L) e
    let s := polynomialBranchEquiv _ _ hp hq E r
    (polynomialBranchAlgEquiv _ _ hp hq E r).toRingHom.comp
        (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L) p r.val.val r.property) =
      (Polynomial.LocalResidue.adjoinRootMap
        (algebraMap k L) q s.val.val s.property).comp e.toRingHom := by
  dsimp only
  apply RingHom.ext
  intro x
  exact scalarBranchAlgEquiv_adjoinRootMap p q e r x

/-- Every factor of p over its own root field has degree below the original
nonlinear degree. Normality, a splitting field and a prime-degree hypothesis
are all unnecessary. -/
theorem original_root_field_decrease (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hdeg : 1 < p.natDegree)
    (r : IrreducibleBranch (p.map (algebraMap k (AdjoinRoot p)))) :
    r.val.val.natDegree < p.natDegree :=
  scalarBranch_natDegree_lt_of_rootHom p hp hdeg (AlgHom.id k (AdjoinRoot p)) r

/-- The second presentation also has a root in the first root field, so its
entire factor family has strictly smaller degree as required by induction. -/
theorem other_presentation_decrease (p q : k[X]) (hq : q.Monic)
    [Fact (Irreducible p)] [Fact (Irreducible q)] (hdeg : 1 < q.natDegree)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (r : IrreducibleBranch (q.map (algebraMap k (AdjoinRoot p)))) :
    r.val.val.natDegree < q.natDegree :=
  scalarBranch_natDegree_lt_of_rootHom q hq hdeg e.symm.toAlgHom r

end AglibTest.GeneralMilnorPolynomialNormBranches

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.AdjoinRootCoefficientEquiv,
    `Aglib.RingTheory.AdjoinRootScalarBranches,
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
    `AglibTest.GeneralMilnorPolynomialNormBranches]
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
  logInfo m!"Checked {names.size} branch comparison and degree-descent declarations: \
    standard axioms only."
