/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootNestedBranches
import Lean.Util.CollectAxioms

/-! Direct consumers of the complete branch bijection and both actual field maps. -/

open Polynomial Polynomial.LocalResidue

namespace AglibTest.AdjoinRootNestedBranches

variable {k S E : Type*} [Field k] [CharZero k] [Field S] [Algebra k S]
  [Field E] [Algebra k E] (p h : k[X]) (hp : p.Monic)
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  [Algebra (AdjoinRoot p) E] [IsScalarTower k (AdjoinRoot p) E]
  (q : (AdjoinRoot p)[X]) [Fact (Irreducible q)]
  (η : AdjoinRoot h ≃ₐ[k] E) (ε : AdjoinRoot q ≃ₐ[AdjoinRoot p] E)

attribute [local instance] AdjoinRoot.scalarBranchAlgebra

/-- The inverse equivalence includes every original direct upper branch. -/
theorem all_direct_branches (t : AdjoinRoot.IrreducibleBranch (h.map (algebraMap k S))) :
    AdjoinRoot.nestedBranchEquiv p h hp q η ε
      ((AdjoinRoot.nestedBranchEquiv p h hp q η ε).symm t) = t :=
  (AdjoinRoot.nestedBranchEquiv p h hp q η ε).apply_symm_apply t

/-- No nested pair is lost or counted twice. -/
theorem all_nested_branches (u : AdjoinRoot.NestedScalarBranch (S := S) p q) :
    (AdjoinRoot.nestedBranchEquiv p h hp q η ε).symm
      (AdjoinRoot.nestedBranchEquiv p h hp q η ε u) = u :=
  (AdjoinRoot.nestedBranchEquiv p h hp q η ε).symm_apply_apply u

/-- The matched residue equivalence preserves exactly the native S algebra. -/
theorem actual_scalar_map (u : AdjoinRoot.NestedScalarBranch (S := S) p q) (b : S) :
    AdjoinRoot.nestedBranchAlgEquiv p h hp q η ε u
      (algebraMap S
        (AdjoinRoot (AdjoinRoot.nestedBranchEquiv p h hp q η ε u).val.val) b) =
      algebraMap (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val)
        (algebraMap S (AdjoinRoot u.1.val.val) b) :=
  (AdjoinRoot.nestedBranchAlgEquiv p h hp q η ε u).commutes b

/-- The full field map from the original E commutes literally, through
the two supplied original polynomial presentations. -/
theorem actual_upper_map (u : AdjoinRoot.NestedScalarBranch (S := S) p q) :
    (AdjoinRoot.nestedBranchAlgEquiv p h hp q η ε u).toRingHom.comp
      ((adjoinRootMap (algebraMap k S) h
        (AdjoinRoot.nestedBranchEquiv p h hp q η ε u).val.val
        (AdjoinRoot.nestedBranchEquiv p h hp q η ε u).property).comp η.symm.toRingHom) =
      (adjoinRootMap (algebraMap (AdjoinRoot p) (AdjoinRoot u.1.val.val)) q
        u.2.val.val u.2.property).comp ε.symm.toRingHom :=
  AdjoinRoot.nestedBranchAlgEquiv_comp_originalMap p h hp q η ε u

end AglibTest.AdjoinRootNestedBranches

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModules := #[`Aglib.RingTheory.AdjoinRootPiBranches,
    `Aglib.RingTheory.AdjoinRootNestedBranches]
  let mut names : NameSet := {}
  for sourceModule in sourceModules do
    let mut found := false
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == sourceModule then
        found := true
        for name in env.header.moduleData[i]!.constNames do
          names := names.insert name
    unless found do
      throwError "The actual source module {sourceModule} is missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.AdjoinRootNestedBranches).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} literal nested-branch declarations: standard axioms only."
