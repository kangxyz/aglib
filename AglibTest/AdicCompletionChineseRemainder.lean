/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdicCompletion.ChineseRemainder
import Lean.Util.CollectAxioms

/-! Literal semilocal completion product and its original coefficient maps. -/

open Function

namespace AglibTest.AdicCompletionChineseRemainder

variable {R ι : Type*} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))

/-- Original ring elements enter each completed branch through its native map. -/
theorem actual_diagonal (r : R) (i : ι) :
    AdicCompletion.prodCompletionAlgEquiv J hJ
      (algebraMap R (AdicCompletion (∏ i, J i) R) r) i =
        algebraMap R (AdicCompletion (J i) R) r :=
  AdicCompletion.prodCompletionAlgEquiv_algebraMap J hJ r i

end AglibTest.AdicCompletionChineseRemainder

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[`AdicCompletion.prodCompletionAlgEquiv,
    `AdicCompletion.prodCompletionAlgEquiv_algebraMap,
    `AglibTest.AdicCompletionChineseRemainder.actual_diagonal]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual completion CRT product: transitive standard axioms only."
