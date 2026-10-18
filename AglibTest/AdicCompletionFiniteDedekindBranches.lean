/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdicCompletion.FiniteDedekindBranches
import Lean.Util.CollectAxioms

/-! Actual finite algebra tensor product, all original localization branches. -/

namespace AglibTest.AdicCompletionFiniteDedekindBranches

open IsLocalRing AdicCompletion
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [IsNoetherianRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [DecidableEq (Ideal S)]

/-- Original finite algebra elements have exactly their original local images. -/
theorem actual_branch_value (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0)
    (s : S) (q : IdealBranch (I.map (algebraMap R S))) :
    tensorEquivLocalCompletions I hI (1 ⊗ₜ[R] s) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap S (Localization.AtPrime q.val) s) :=
  tensorEquivLocalCompletions_one_tmul I hI s q

end AglibTest.AdicCompletionFiniteDedekindBranches

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[`AdicCompletion.tensorEquivLocalCompletions,
    `AdicCompletion.tensorEquivLocalCompletions_one_tmul,
    `AdicCompletion.dedekindBranchesAlgEquiv,
    `AdicCompletion.localizationAlgEquiv,
    `AglibTest.AdicCompletionFiniteDedekindBranches.actual_branch_value]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual full finite Dedekind completion branch tensor: transitive standard axioms only."
