/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding
import Lean.Util.CollectAxioms

/-! Direct consumers for every intermediate-field branch and actual Sylow branches. -/

namespace AglibTest.AdjoinRootSplitBranchEmbedding

open Polynomial IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- No ambient finiteness, Galois, characteristic, or monicity premise is
required for the embedding of any actual branch into a splitting overfield. -/
theorem every_intermediate_branch (L : IntermediateField k Ω)
    (p : k[X]) (hp : p ≠ 0) (hsplit : (p.map (algebraMap k Ω)).Splits)
    (q : AdjoinRoot.IrreducibleBranch (p.map (algebraMap k L))) :
    Nonempty (AdjoinRoot q.val.val →ₐ[L] Ω) ∧ q.val.val.natDegree ≤ p.natDegree :=
  AdjoinRoot.nonempty_algHom_branch_of_splits p hp hsplit q

/-- A Sylow branch has the literal field embedding, degree bound, and
relative p-group Galois ambient needed for the smaller-degree induction. -/
theorem every_sylow_branch [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) (S : Sylow ℓ (Ω ≃ₐ[k] Ω))
    (p : k[X]) (hp : p ≠ 0) (hsplit : (p.map (algebraMap k Ω)).Splits)
    (q : AdjoinRoot.IrreducibleBranch
      (p.map (algebraMap k (fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))))) :
    Nonempty (AdjoinRoot q.val.val →ₐ[fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      q.val.val.natDegree ≤ p.natDegree ∧
      IsPGroup ℓ (Ω ≃ₐ[fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))] Ω) ∧
      IsGalois (fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))) Ω := by
  obtain ⟨hembedding, hdegree⟩ :=
    AdjoinRoot.nonempty_algHom_branch_of_splits p hp hsplit q
  exact ⟨hembedding, hdegree, isPGroup_aut_over_sylow_fixedField ℓ S, inferInstance⟩

end AglibTest.AdjoinRootSplitBranchEmbedding

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.isEmpty then
    throwError "The actual split-branch source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootSplitBranchEmbedding).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} split-branch embedding declarations: standard axioms only."
