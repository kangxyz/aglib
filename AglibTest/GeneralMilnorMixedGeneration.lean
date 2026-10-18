/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.MixedGeneration
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of bounded Bass--Tate mixed generation and actual finite
expansions. The linear, quadratic, degree-one Milnor, and positive characteristic
cases are retained. Checked bodies are audited through legacy imports. -/

open Polynomial MilnorK MilnorK.PolynomialResidue

namespace AglibTest.GeneralMilnorMixedGeneration

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The polynomial stage collapses without any special-field construction. -/
theorem actual_stage_bound (m d : ℕ)
    (hgap : ∀ q : MonicIrreducible k, q.val.natDegree < d → q.val.natDegree = 1) :
    DegreeFiltration.lower k (m + 1) d ≤ DegreeFiltration.lower k (m + 1) 2 :=
  DegreeFiltration.lower_le_lower_two_of_degree_gap m d hgap

/-- The actual root-field Milnor quotient is generated, not a replacement module. -/
theorem actual_mixed_span (p : MonicIrreducible k)
    (hgap : ∀ q : MonicIrreducible k,
      q.val.natDegree < p.val.natDegree → q.val.natDegree = 1) (m : ℕ) :
    mixedSpan (algebraMap k (AdjoinRoot p.val)) m = ⊤ :=
  mixedSpan_eq_top_of_degree_gap p hgap m

/-- For a literal linear modulus there are no smaller positive degrees. -/
theorem linear_modulus (m : ℕ) :
    mixedSpan (algebraMap k (AdjoinRoot (X : k[X]))) m = ⊤ :=
  mixedSpan_eq_top_of_natDegree_le_two ⟨X, monic_X, irreducible_X⟩ (by simp) m

/-- Every quadratic extension is included without a separability hypothesis. -/
theorem quadratic_modulus (p : MonicIrreducible k) (hp : p.val.natDegree = 2) (m : ℕ) :
    mixedSpan (algebraMap k (AdjoinRoot p.val)) m = ⊤ :=
  mixedSpan_eq_top_of_natDegree_le_two p (by omega) m

/-- The same quadratic assertion is meaningful in characteristic two. -/
theorem characteristic_two (p : MonicIrreducible (ZMod 2))
    (hp : p.val.natDegree = 2) (m : ℕ) :
    mixedSpan (algebraMap (ZMod 2) (AdjoinRoot p.val)) m = ⊤ :=
  mixedSpan_eq_top_of_natDegree_le_two p (by omega) m

/-- An empty base prefix gives degree-one classes in the original unit group. -/
theorem empty_prefix (p : MonicIrreducible k)
    (hgap : ∀ q : MonicIrreducible k,
      q.val.natDegree < p.val.natDegree → q.val.natDegree = 1) :
    mixedSpan (algebraMap k (AdjoinRoot p.val)) 0 = ⊤ :=
  mixedSpan_eq_top_of_degree_gap p hgap 0

/-- Every class is supplied with finite coefficient and unit-tuple witnesses. -/
theorem actual_finite_expansion (p : MonicIrreducible k)
    (hgap : ∀ q : MonicIrreducible k,
      q.val.natDegree < p.val.natDegree → q.val.natDegree = 1) (m : ℕ)
    (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ c : (SymbolTuple k m × (AdjoinRoot p.val)ˣ) →₀ ℤ,
      (c.sum fun ab z => z • symbol (Fin.snoc
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ ab.1) ab.2)) = x :=
  exists_mixed_expansion_of_degree_gap p hgap m x

/-- A substantive consumer: equality on mixed symbols determines maps on every
root-field class because the finite expansion has actually been proved. -/
theorem maps_equal_on_mixed (p : MonicIrreducible k)
    (hgap : ∀ q : MonicIrreducible k,
      q.val.natDegree < p.val.natDegree → q.val.natDegree = 1) (m : ℕ)
    {A : Type*} [AddCommGroup A] [Module ℤ A]
    (f g : K (AdjoinRoot p.val) (m + 1) →ₗ[ℤ] A)
    (hfg : ∀ (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ),
      f (symbol (Fin.snoc
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b)) =
      g (symbol (Fin.snoc
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b))) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := exists_mixed_expansion_of_degree_gap p hgap m x
  simp only [Finsupp.sum, map_sum, LinearMap.map_smul, hfg]

end AglibTest.GeneralMilnorMixedGeneration

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorMixedGeneration]
  let selectedDeclaration (name : Name) := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} mixed generation and general Milnor declarations: \
    standard axioms only."
