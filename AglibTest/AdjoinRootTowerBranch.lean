/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootTowerBranch
import Lean.Util.CollectAxioms

/-! The branch chosen by an actual root-field inclusion retains both original
maps, the specified roots, and the actual tower degree. No norm law is imported. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot

namespace AglibTest.AdjoinRootTowerBranch

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

/-- The constructed equivalence is exactly tensor swapping followed by
literal evaluation, as required by the tower consumer. -/
theorem actual_equivalence (f : AdjoinRoot p →ₐ[k] AdjoinRoot h) :
    towerBranchRingEquiv p h f =
      (tensorSwapBranchRingEquiv p h (towerBranch p h f)).trans
        (towerBranchTargetEquiv p h f).toRingEquiv := rfl

/-- The original upper-field coefficient map is an actual inverse, on every element. -/
theorem actual_upper_inverse (f : AdjoinRoot p →ₐ[k] AdjoinRoot h) (a : AdjoinRoot h) :
    (towerBranchRingEquiv p h f).symm a =
      adjoinRootMap (algebraMap k (AdjoinRoot p)) h (towerBranch p h f).val.val
        (towerBranch p h f).property a :=
  RingHom.congr_fun (towerBranchRingEquiv_symm_toRingHom p h f) a

/-- The original embedding, not an unspecified conjugate, is recovered on coefficients. -/
theorem actual_lower_embedding (f : AdjoinRoot p →ₐ[k] AdjoinRoot h) (a : AdjoinRoot p) :
    towerBranchRingEquiv p h f
      (algebraMap (AdjoinRoot p) (AdjoinRoot (towerBranch p h f).val.val) a) = f a :=
  towerBranchRingEquiv_algebraMap p h f a

/-- The scalar branch has the exact relative degree in the original tower. -/
theorem actual_degree_product (hp : p.Monic) (hh : h.Monic)
    (f : AdjoinRoot p →ₐ[k] AdjoinRoot h) :
    p.natDegree * (towerBranch p h f).val.val.natDegree = h.natDegree :=
  towerBranch_natDegree_mul p h hp hh f

end AglibTest.AdjoinRootTowerBranch

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `AdjoinRoot.towerLinearBranch,
    `AdjoinRoot.towerBranch,
    `AdjoinRoot.towerBranch_matched_polynomial,
    `AdjoinRoot.towerBranch_matched_natDegree,
    `AdjoinRoot.towerBranchTargetEquiv,
    `AdjoinRoot.towerBranchTargetEquiv_mk,
    `AdjoinRoot.towerBranchTargetEquiv_root,
    `AdjoinRoot.towerBranchRingEquiv,
    `AdjoinRoot.towerBranchTargetEquiv_comp_adjoinRootMap,
    `AdjoinRoot.towerBranchRingEquiv_algebraMap,
    `AdjoinRoot.towerBranchRingEquiv_adjoinRootMap,
    `AdjoinRoot.towerBranchRingEquiv_root,
    `AdjoinRoot.towerBranchRingEquiv_symm_toRingHom,
    `AdjoinRoot.towerBranch_natDegree_mul,
    `AglibTest.AdjoinRootTowerBranch.actual_equivalence,
    `AglibTest.AdjoinRootTowerBranch.actual_upper_inverse,
    `AglibTest.AdjoinRootTowerBranch.actual_lower_embedding,
    `AglibTest.AdjoinRootTowerBranch.actual_degree_product]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the actual root-field tower branch and both original maps: standard axioms only."
