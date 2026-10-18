/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.FiniteMixedGeneration
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers of finite classwise mixed generation, including literal
irreducibility transport, characteristic zero, characteristic two, and the
empty base prefix. The class is always from the original Milnor quotient. -/

open Polynomial MilnorK PolynomialResidue Polynomial.LocalResidue

namespace AglibTest.GeneralMilnorFiniteMixedGeneration

universe u

/-- The intended characteristic-zero application returns actual finite signed coefficients. -/
theorem characteristic_zero {k : Type u} [Field k] [CharZero k]
    (p : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      ∃ q : MonicIrreducible L, q.val = p.val.map (algebraMap k L) ∧
        ∃ hq : q.val ∣ p.val.map (algebraMap k L),
          ∃ c : (SymbolTuple L m × (AdjoinRoot q.val)ˣ) →₀ ℤ,
            (c.sum fun ab z => z • symbol (Fin.snoc
              (Units.map (algebraMap L (AdjoinRoot q.val)).toMonoidHom ∘ ab.1) ab.2)) =
                map (m + 1) (adjoinRootMap (algebraMap k L) p.val q.val hq) x :=
  exists_finite_coprime_mixed_expansion p hp m x

/-- The finite expansion gives actual mixed-span membership and preserves the full degree. -/
theorem actual_mixed_membership {k : Type u} [Field k] [PerfectField k]
    (p : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      ∃ q : MonicIrreducible L, q.val.natDegree = p.val.natDegree ∧
        q.val = p.val.map (algebraMap k L) ∧
        ∃ hq : q.val ∣ p.val.map (algebraMap k L),
          map (m + 1) (adjoinRootMap (algebraMap k L) p.val q.val hq) x ∈
            mixedSpan (algebraMap L (AdjoinRoot q.val)) m := by
  obtain ⟨L, hL, hA, hfd, hsep, hcop, q, heq, hq, c, hc⟩ :=
    exists_finite_coprime_mixed_expansion p hp m x
  refine ⟨L, hL, hA, hfd, hsep, hcop, q, ?_, heq, hq, ?_⟩
  · rw [heq, Polynomial.natDegree_map]
  · rw [← hc]
    exact Submodule.sum_mem _ fun ab _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨ab.1, ab.2, rfl⟩)

/-- The empty prefix is literal, so the endpoint covers Milnor degree one. -/
theorem empty_prefix {k : Type u} [Field k] [PerfectField k]
    (p : MonicIrreducible k) (hp : p.val.natDegree.Prime) (x : K (AdjoinRoot p.val) 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      ∃ q : MonicIrreducible L, q.val.natDegree = p.val.natDegree ∧
        q.val = p.val.map (algebraMap k L) ∧
        ∃ hq : q.val ∣ p.val.map (algebraMap k L),
          map 1 (adjoinRootMap (algebraMap k L) p.val q.val hq) x ∈
            mixedSpan (algebraMap L (AdjoinRoot q.val)) 0 :=
  actual_mixed_membership p hp 0 x

/-- Positive characteristic needs only the explicit perfect-base instance. -/
theorem characteristic_two (p : MonicIrreducible (ZMod 2)) (hp : p.val.natDegree.Prime)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod 2) L),
      FiniteDimensional (ZMod 2) L ∧ Algebra.IsSeparable (ZMod 2) L ∧
      p.val.natDegree.Coprime (Module.finrank (ZMod 2) L) ∧
      ∃ q : MonicIrreducible L, q.val.natDegree = p.val.natDegree ∧
        q.val = p.val.map (algebraMap (ZMod 2) L) ∧
        ∃ hq : q.val ∣ p.val.map (algebraMap (ZMod 2) L),
          map (m + 1) (adjoinRootMap (algebraMap (ZMod 2) L) p.val q.val hq) x ∈
            mixedSpan (algebraMap L (AdjoinRoot q.val)) m :=
  actual_mixed_membership p hp m x

end AglibTest.GeneralMilnorFiniteMixedGeneration

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FiniteCoprimeSplitting,
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.SylowFixedField,
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialPlaceContraction,
    `Aglib.RingTheory.PolynomialResidueBaseChange]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorFiniteMixedGeneration]
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
  logInfo m!"Checked {names.size} finite mixed-generation and general Milnor declarations: \
    standard axioms only."
