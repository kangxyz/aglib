/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.AdjoinRootCoefficientTowerBranches
import Lean.Util.CollectAxioms

/-! Consumers of the complete coefficient-tower factor bijection and actual field maps. -/

open Polynomial Polynomial.LocalResidue AdjoinRoot

namespace AglibTest.AdjoinRootCoefficientTowerBranches

noncomputable section

variable {k L E : Type*} [Field k] [Field L] [Field E]

/-- Every direct upper factor appears exactly once. -/
theorem all_direct_branches (φ : k →+* L) (ψ : L →+* E) (h : k[X]) (hh : h ≠ 0)
    (q : IrreducibleBranch (h.map (ψ.comp φ))) :
    coefficientTowerBranchEquiv φ ψ h hh
      ((coefficientTowerBranchEquiv φ ψ h hh).symm q) = q :=
  (coefficientTowerBranchEquiv φ ψ h hh).apply_symm_apply q

/-- Reindexing preserves the upper quotient type definitionally. -/
def actual_upper_field (φ : k →+* L) (ψ : L →+* E) (h : k[X]) (hh : h ≠ 0)
    (u : CoefficientTowerBranch φ ψ h) :
    AdjoinRoot (coefficientTowerBranchEquiv φ ψ h hh u).val.val ≃+*
      AdjoinRoot u.2.val.val :=
  RingEquiv.refl _

/-- The native direct coefficient map is recovered for an actual algebra tower. -/
def actual_algebra_tower_branches [Algebra k L] [Algebra L E] [Algebra k E]
    [IsScalarTower k L E] (h : k[X]) (hh : h ≠ 0) :
    CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h ≃
      IrreducibleBranch (h.map (algebraMap k E)) :=
  coefficientTowerBranchEquivOfAlgebra (L := L) h hh

/-- Even with the native direct algebra map, the original upper residue field is literal. -/
def actual_native_upper_field [Algebra k L] [Algebra L E] [Algebra k E]
    [IsScalarTower k L E] (h : k[X]) (hh : h ≠ 0)
    (u : CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h) :
    AdjoinRoot (coefficientTowerBranchEquivOfAlgebra (L := L) h hh u).val.val ≃+*
      AdjoinRoot u.2.val.val :=
  RingEquiv.refl _

/-- The native direct quotient map supplies exactly the algebra in the branch field tower. -/
theorem actual_native_residue_tower [Algebra k L] [Algebra L E] [Algebra k E]
    [IsScalarTower k L E] (h : k[X]) [Fact (Irreducible h)]
    (u : CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h) :
    letI := (adjoinRootMap (algebraMap k L) h u.1.val.val u.1.property).toAlgebra
    letI := (adjoinRootMap (algebraMap L E) u.1.val.val u.2.val.val u.2.property).toAlgebra
    letI := (adjoinRootMap (algebraMap k E) h u.2.val.val
      (coefficientTowerBranchOfAlgebra (L := L) h u).property).toAlgebra
    IsScalarTower (AdjoinRoot h) (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val) :=
  adjoinRootMap_isScalarTowerOfAlgebra h u.1.val.val u.2.val.val
    u.1.property u.2.property (coefficientTowerBranchOfAlgebra (L := L) h u).property

/-- The original residue-field maps, not replacement embeddings, form the tower. -/
theorem actual_residue_tower (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) [Fact (Irreducible h)] (u : CoefficientTowerBranch φ ψ h) :
    letI := (adjoinRootMap φ h u.1.val.val u.1.property).toAlgebra
    letI := (adjoinRootMap ψ u.1.val.val u.2.val.val u.2.property).toAlgebra
    letI := (adjoinRootMap (ψ.comp φ) h u.2.val.val
      (coefficientTowerBranch φ ψ h u).property).toAlgebra
    IsScalarTower (AdjoinRoot h) (AdjoinRoot u.1.val.val) (AdjoinRoot u.2.val.val) :=
  adjoinRootMap_isScalarTower φ ψ h u.1.val.val u.2.val.val
    u.1.property u.2.property (coefficientTowerBranch φ ψ h u).property

/-- Full finite sums reindex without multiplicity or missing-factor assumptions. -/
theorem all_factor_sum (φ : k →+* L) (ψ : L →+* E) (h : k[X]) (hh : h ≠ 0)
    [Fintype (IrreducibleBranch (h.map φ))]
    [∀ r : IrreducibleBranch (h.map φ), Fintype (IrreducibleBranch (r.val.val.map ψ))]
    [Fintype (IrreducibleBranch (h.map (ψ.comp φ)))]
    {A : Type*} [AddCommMonoid A] (f : E[X] → A) :
    ∑ q : IrreducibleBranch (h.map (ψ.comp φ)), f q.val.val =
      ∑ r : IrreducibleBranch (h.map φ),
        ∑ q : IrreducibleBranch (r.val.val.map ψ), f q.val.val :=
  sum_coefficientTowerBranchEquiv φ ψ h hh (fun q => f q.val.val)

end

end AglibTest.AdjoinRootCoefficientTowerBranches

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.RingTheory.AdjoinRootCoefficientTowerBranches
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
    if (`AglibTest.AdjoinRootCoefficientTowerBranches).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} coefficient-tower branch declarations: standard axioms only."
