/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.SplitPolynomialGeneration
import Lean.Util.CollectAxioms

/-! Direct consumers of the finite split-polynomial bridge. No global degree
restriction on irreducible polynomials or special-field instance is supplied.
Legacy imports allow complete checked-proof-body axiom inspection. -/

open Polynomial Polynomial.LocalResidue MilnorK
open MilnorK.PolynomialResidue MilnorK.DegreeFiltration

namespace AglibTest.GeneralMilnorSplitPolynomialGeneration

variable {k L : Type*} [Field k] [Field L]

/-- Every nonzero split-coordinate tuple lies in the literal second stage. -/
theorem actual_split_stage (n : ℕ) (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (hsplit : ∀ i, (a i).Splits) :
    symbol (polynomialTuple a ha) ∈ lower k n 2 :=
  polynomial_symbol_mem_lower_two_of_splits n a ha hsplit

/-- Repeated linear factors/entries are permitted by the actual multilinearity proof. -/
theorem repeated_linear_entries (n : ℕ) (c : k) :
    symbol (polynomialTuple (fun _ : Fin n => X - C c)
      (fun _ => X_sub_C_ne_zero c)) ∈ lower k n 2 :=
  polynomial_symbol_mem_lower_two_of_splits n _ _ (fun _ => Splits.X_sub_C c)

/-- The empty tuple belongs to the same actual stage. -/
theorem empty_tuple_stage :
    symbol (polynomialTuple (Fin.elim0 : Fin 0 → k[X]) (fun i => Fin.elim0 i)) ∈
      lower k 0 2 :=
  polynomial_symbol_mem_lower_two_of_splits 0 _ _ (fun i => Fin.elim0 i)

/-- Coefficient restriction uses the actual rational-function map. -/
theorem coefficient_extension (φ : k →+* L) (n : ℕ) (a : Fin n → k[X])
    (ha : ∀ i, a i ≠ 0) (hsplit : ∀ i, ((a i).map φ).Splits) :
    map n (fractionMap φ) (symbol (polynomialTuple a ha)) ∈ lower L n 2 :=
  map_polynomial_symbol_mem_lower_two_of_splits φ n a ha hsplit

/-- Literal specialization produces the actual mixed span. -/
theorem actual_specialization (p : k[X]) [Fact (Irreducible p)]
    (hp : 1 < p.natDegree) (m : ℕ) (a : Fin (m + 1) → k[X])
    (ha : ∀ i, a i ≠ 0) (hsplit : ∀ i, (a i).Splits) :
    specializeAt p (m + 1) (symbol (polynomialTuple a ha)) ∈
      mixedSpan (algebraMap k (AdjoinRoot p)) m :=
  specialize_split_polynomial_mem_mixed p hp m a ha hsplit

/-- The actual irreducible factor and its source divisibility stay explicit. -/
theorem actual_factor_symbol (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) (hq : q.val ∣ p.val.map φ) (m : ℕ)
    (a : SymbolTuple (AdjoinRoot p.val) (m + 1))
    (hsplit : ∀ i, ((reducedRepresentative p.val p.property.1 (a i)).map φ).Splits) :
    map (m + 1) (adjoinRootMap φ p.val q.val hq) (symbol a) ∈
      mixedSpan (algebraMap L (AdjoinRoot q.val)) m :=
  restricted_symbol_mem_mixed_of_reduced_splits φ p q hq m a hsplit

universe u v

/-- One finite family is extracted before choosing any future coefficient field. -/
theorem witnesses_before_scalar_extension {k : Type u} [Field k]
    (p : MonicIrreducible k) (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.val.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : MonicIrreducible L)
        (hq : q.val ∣ p.val.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        map (m + 1) (adjoinRootMap φ p.val q.val hq) x ∈
          mixedSpan (algebraMap L (AdjoinRoot q.val)) m :=
  exists_finite_reduced_splitting_witness p m x

/-- The same witnesses give actual finite signed mixed expansions on all branches. -/
theorem finite_mixed_coefficients {k : Type u} [Field k]
    (p : MonicIrreducible k) (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.val.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : MonicIrreducible L)
        (hq : q.val ∣ p.val.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        ∃ c : (SymbolTuple L m × (AdjoinRoot q.val)ˣ) →₀ ℤ,
          (c.sum fun ab z => z • symbol (Fin.snoc
            (Units.map (algebraMap L (AdjoinRoot q.val)).toMonoidHom ∘ ab.1) ab.2)) =
              map (m + 1) (adjoinRootMap φ p.val q.val hq) x :=
  exists_finite_reduced_mixed_expansion p m x

/-- Degree one of Milnor theory uses the genuine empty base prefix. -/
theorem empty_base_prefix (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) (hq : q.val ∣ p.val.map φ)
    (a : SymbolTuple (AdjoinRoot p.val) 1)
    (hsplit : ∀ i, ((reducedRepresentative p.val p.property.1 (a i)).map φ).Splits) :
    map 1 (adjoinRootMap φ p.val q.val hq) (symbol a) ∈
      mixedSpan (algebraMap L (AdjoinRoot q.val)) 0 :=
  restricted_symbol_mem_mixed_of_reduced_splits φ p q hq 0 a hsplit

end AglibTest.GeneralMilnorSplitPolynomialGeneration

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncCoefficientMap,
    `Aglib.FieldTheory.RatFuncInversion,
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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorSplitPolynomialGeneration]
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
  logInfo m!"Checked {names.size} split-polynomial generation and general Milnor declarations: \
    standard axioms only."
