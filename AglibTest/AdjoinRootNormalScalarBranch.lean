/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.AdjoinRootNormalScalarBranch
import Lean.Util.CollectAxioms

/-! Direct consumers for normality of an actual branch and of the whole scalar image. -/

open Polynomial

namespace AglibTest.AdjoinRootNormalScalarBranch

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  {p : k[X]} [Fact (Irreducible p)] [Normal k (AdjoinRoot p)]

/-- The result applies to every irreducible branch, in arbitrary characteristic. -/
theorem actual_branch_normal (hp : p.Monic) (q : L[X]) [Fact (Irreducible q)]
    (hd : q ∣ p.map (algebraMap k L)) : Normal L (AdjoinRoot q) :=
  AdjoinRoot.normal_of_dvd_map hp hd

/-- In particular, an irreducible whole coefficient image remains normal. -/
theorem whole_coefficient_image_normal (hp : p.Monic)
    [Fact (Irreducible (p.map (algebraMap k L)))] :
    Normal L (AdjoinRoot (p.map (algebraMap k L))) :=
  AdjoinRoot.normal_of_dvd_map hp dvd_rfl

/-- Downstream consumers obtain native normality, not a substitute splitting hypothesis. -/
theorem actual_branch_minpoly_splits (hp : p.Monic) (q : L[X])
    [Fact (Irreducible q)] (hd : q ∣ p.map (algebraMap k L))
    (x : AdjoinRoot q) : ((minpoly L x).map (algebraMap L (AdjoinRoot q))).Splits := by
  let : Normal L (AdjoinRoot q) := AdjoinRoot.normal_of_dvd_map hp hd
  exact Normal.splits (inferInstance : Normal L (AdjoinRoot q)) x

end AglibTest.AdjoinRootNormalScalarBranch

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.FieldTheory.AdjoinRootNormalScalarBranch
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.isEmpty then
    throwError "The actual normal scalar-branch source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootNormalScalarBranch).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} normal scalar-branch declarations: standard axioms only."
