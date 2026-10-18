/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.PrimeNormalScalarDichotomy
import Lean.Util.CollectAxioms

/-! Direct tests for arbitrary scalar extension of a prime-normal polynomial. -/

namespace AglibTest.PrimeNormalScalarDichotomy

noncomputable section

open Polynomial

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K] [CharZero F]
  {p : F[X]} (hp : p.Monic) (hi : Irreducible p) [Fact (Irreducible p)]
  [Normal F (AdjoinRoot p)] (hprime : p.natDegree.Prime)

include hp hi hprime
-- The target field is arbitrary and can lie in a different universe.
theorem arbitrary_extension :
    Irreducible (p.map (algebraMap F K)) ∨ (p.map (algebraMap F K)).Splits :=
  hp.irreducible_map_or_splits_of_prime_normal hi hprime

-- The reducible branch gives complete splitting, not merely one root.
theorem reducible_splits (h : ¬Irreducible (p.map (algebraMap F K))) :
    (p.map (algebraMap F K)).Splits :=
  (hp.irreducible_map_or_splits_of_prime_normal hi hprime).resolve_left h

-- Non-splitting forces the original mapped polynomial itself to be irreducible.
theorem nonsplit_irreducible (h : ¬(p.map (algebraMap F K)).Splits) :
    Irreducible (p.map (algebraMap F K)) :=
  (hp.irreducible_map_or_splits_of_prime_normal hi hprime).resolve_right h

end

end AglibTest.PrimeNormalScalarDichotomy

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `Aglib.FieldTheory.PrimeNormalScalarDichotomy then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 2 then
    throwError "The source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.PrimeNormalScalarDichotomy).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} prime-normal dichotomy declarations: standard axioms only."
