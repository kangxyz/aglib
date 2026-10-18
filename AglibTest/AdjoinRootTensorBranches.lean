/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootTensorBranches
import Lean.Util.CollectAxioms

/-! Direct consumers retaining every tensor branch and both original field maps. -/

open Polynomial AdjoinRoot

namespace AglibTest.AdjoinRootTensorBranches

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

/-- No branch is omitted or identified with a different source branch. -/
theorem every_source_branch (q : IrreducibleBranch hE) :
    (tensorSwapBranchEquiv p h).symm (tensorSwapBranchEquiv p h q) = q :=
  (tensorSwapBranchEquiv p h).symm_apply_apply q

/-- Every target branch, including a nonsplit factor, occurs in the correspondence. -/
theorem every_target_branch (r : IrreducibleBranch pH) :
    tensorSwapBranchEquiv p h ((tensorSwapBranchEquiv p h).symm r) = r :=
  (tensorSwapBranchEquiv p h).apply_symm_apply r

/-- The quotient-field comparison agrees on every whole-algebra class. -/
theorem actual_quotient_square (q : IrreducibleBranch hE) (x : AdjoinRoot hE) :
    tensorSwapBranchRingEquiv p h q (divisorMap hE q.val.val q.property x) =
      divisorMap pH (tensorSwapBranchEquiv p h q).val.val
        (tensorSwapBranchEquiv p h q).property (tensorSwapEquiv p h x) :=
  tensorSwapBranchRingEquiv_divisorMap p h q x

/-- Original coefficients from `E` map through the actual residue quotient map on the right. -/
theorem actual_first_field_square (q : IrreducibleBranch hE) (a : E) :
    tensorSwapBranchRingEquiv p h q (algebraMap E (AdjoinRoot q.val.val) a) =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k H) p
        (tensorSwapBranchEquiv p h q).val.val (tensorSwapBranchEquiv p h q).property a :=
  tensorSwapBranchRingEquiv_algebraMap p h q a

/-- The original `H` residue map becomes the literal coefficient inclusion on the right. -/
theorem actual_second_field_square (q : IrreducibleBranch hE) (b : H) :
    tensorSwapBranchRingEquiv p h q
      (Polynomial.LocalResidue.adjoinRootMap (algebraMap k E) h q.val.val q.property b) =
      algebraMap H (AdjoinRoot (tensorSwapBranchEquiv p h q).val.val) b :=
  tensorSwapBranchRingEquiv_adjoinRootMap p h q b

/-- The branch-field equivalence has an actual inverse on all elements. -/
theorem branch_field_inverse (q : IrreducibleBranch hE) (x : AdjoinRoot q.val.val) :
    (tensorSwapBranchRingEquiv p h q).symm (tensorSwapBranchRingEquiv p h q x) = x :=
  (tensorSwapBranchRingEquiv p h q).symm_apply_apply x

end AglibTest.AdjoinRootTensorBranches

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.RingTheory.AdjoinRootTensorBranches
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 10 then
    throwError "The actual tensor-branch source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootTensorBranches).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} tensor branch and consumer declarations: standard axioms only."
