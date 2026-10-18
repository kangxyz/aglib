/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootScalarBranchCoefficientEquiv
import Lean.Util.CollectAxioms

/-! Direct consumers of literal branch and root-map coefficient transport. -/

open Polynomial AdjoinRoot

namespace AglibTest.AdjoinRootScalarBranchCoefficientEquiv

variable {k A B : Type*} [Field k] [Field A] [Field B]
  [Algebra k A] [Algebra k B] (ε : A ≃ₐ[k] B) (h : k[X])

/-- The target polynomial is the literal map, with no normalization or cast. -/
theorem literal_polynomial (r : IrreducibleBranch (h.map (algebraMap k A))) :
    (scalarBranchCoefficientEquiv ε h r).val.val = r.val.val.map ε.toRingHom := rfl

/-- Every target branch is included exactly once. -/
theorem all_target_branches (r : IrreducibleBranch (h.map (algebraMap k B))) :
    scalarBranchCoefficientEquiv ε h ((scalarBranchCoefficientEquiv ε h).symm r) = r :=
  (scalarBranchCoefficientEquiv ε h).apply_symm_apply r

/-- Every source branch is recovered by the inverse coefficient equivalence. -/
theorem all_source_branches (r : IrreducibleBranch (h.map (algebraMap k A))) :
    (scalarBranchCoefficientEquiv ε h).symm (scalarBranchCoefficientEquiv ε h r) = r :=
  (scalarBranchCoefficientEquiv ε h).symm_apply_apply r

attribute [local instance] scalarBranchAlgebra

variable [Fact (Irreducible h)]

/-- The exact original native quotient map is retained definitionally. -/
theorem native_underlying_map (r : IrreducibleBranch (h.map (algebraMap k A))) :
    (scalarBranchCoefficientAlgEquiv ε h r).toRingHom =
      (mapRingEquiv ε.toRingEquiv r.val.val (r.val.val.map ε.toRingHom)
        (Associated.refl _)).toRingHom := rfl

/-- The original lower quotient maps commute on every class. -/
theorem original_lower_map (r : IrreducibleBranch (h.map (algebraMap k A)))
    (x : AdjoinRoot h) :
    scalarBranchCoefficientAlgEquiv ε h r
        (Polynomial.LocalResidue.adjoinRootMap (algebraMap k A) h r.val.val r.property x) =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k B) h
        (scalarBranchCoefficientEquiv ε h r).val.val
        (scalarBranchCoefficientEquiv ε h r).property x :=
  (scalarBranchCoefficientAlgEquiv ε h r).commutes x

end AglibTest.AdjoinRootScalarBranchCoefficientEquiv

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.RingTheory.AdjoinRootScalarBranchCoefficientEquiv
  let mut names : NameSet := {}
  let mut found := false
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      found := true
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  unless found do
    throwError "The actual source module {sourceModule} is missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootScalarBranchCoefficientEquiv).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} scalar-branch coefficient declarations: standard axioms only."
