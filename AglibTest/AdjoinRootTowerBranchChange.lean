/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootTowerBranchChange
import Lean.Util.CollectAxioms

/-! Actual relative presentation change, retaining the original coefficient
maps and the strict degree decrease needed for strong induction. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot

namespace AglibTest.AdjoinRootTowerBranchChange

variable {k : Type*} [Field k] (p h₁ h₂ : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h₁)] [Fact (Irreducible h₂)]

/-- The constructed comparison fixes the unchanged lower field pointwise. -/
theorem actual_relative_algebra_map
    (e : AdjoinRoot h₁ ≃ₐ[k] AdjoinRoot h₂)
    (f : AdjoinRoot p →ₐ[k] AdjoinRoot h₁) (a : AdjoinRoot p) :
    towerBranchChangeAlgEquiv p h₁ h₂ e f
      (algebraMap (AdjoinRoot p) (AdjoinRoot (towerBranch p h₁ f).val.val) a) =
        algebraMap (AdjoinRoot p)
          (AdjoinRoot (towerBranch p h₂ (e.toAlgHom.comp f)).val.val) a :=
  (towerBranchChangeAlgEquiv p h₁ h₂ e f).commutes a

/-- The complete original upper quotient map, rather than only its root,
is preserved by the actual relative equivalence. -/
theorem actual_upper_quotient_square
    (e : AdjoinRoot h₁ ≃ₐ[k] AdjoinRoot h₂)
    (f : AdjoinRoot p →ₐ[k] AdjoinRoot h₁) :
    (towerBranchChangeAlgEquiv p h₁ h₂ e f).toRingHom.comp
      (adjoinRootMap (algebraMap k (AdjoinRoot p)) h₁ (towerBranch p h₁ f).val.val
        (towerBranch p h₁ f).property) =
      (adjoinRootMap (algebraMap k (AdjoinRoot p)) h₂
        (towerBranch p h₂ (e.toAlgHom.comp f)).val.val
        (towerBranch p h₂ (e.toAlgHom.comp f)).property).comp e.toRingHom :=
  towerBranchChangeAlgEquiv_comp_adjoinRootMap p h₁ h₂ e f

/-- The literal relative source polynomial has strictly smaller degree. -/
theorem actual_strict_degree_drop (hp : p.Monic) (hh : h₁.Monic)
    (hdeg : 1 < p.natDegree) (f : AdjoinRoot p →ₐ[k] AdjoinRoot h₁) :
    (towerBranch p h₁ f).val.val.natDegree < h₁.natDegree :=
  towerBranch_natDegree_lt p h₁ hp hh hdeg f

end AglibTest.AdjoinRootTowerBranchChange

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `AdjoinRoot.towerBranchChangeAlgEquiv,
    `AdjoinRoot.towerBranchChangeAlgEquiv_adjoinRootMap,
    `AdjoinRoot.towerBranchChangeAlgEquiv_comp_adjoinRootMap,
    `AdjoinRoot.towerBranchRingEquiv_change,
    `AdjoinRoot.towerBranchChange_natDegree,
    `AdjoinRoot.towerBranch_natDegree_lt,
    `AglibTest.AdjoinRootTowerBranchChange.actual_relative_algebra_map,
    `AglibTest.AdjoinRootTowerBranchChange.actual_upper_quotient_square,
    `AglibTest.AdjoinRootTowerBranchChange.actual_strict_degree_drop]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked actual tower-branch change and degree descent: standard axioms only."
