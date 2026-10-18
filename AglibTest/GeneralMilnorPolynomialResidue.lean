/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Polynomial.Support
import Aglib.KTheory.MilnorK.InfinityDegree
import Lean.Util.CollectAxioms

/-! Actual finite and infinity residue consumers in every degree. These tests
retain last-slot signs in odd target degree, the degree-one empty prefix,
nonmonic polynomials, constant polynomials, and dependent finite support. -/

open MilnorK Polynomial
open MilnorK.PolynomialResidue

namespace AglibTest.GeneralMilnorPolynomialResidue

variable (k : Type*) [Field k]

/-- Finite polynomial residue agrees with the canonical actual DVR construction. -/
theorem canonical_finite (p : k[X]) [Fact (Irreducible p)] (n : ℕ) :
    residueAt p n = (MilnorK.map n (Polynomial.LocalResidue.residueEquiv p).toRingHom).comp
      (DVR.residue (Polynomial.LocalResidue.Ring p) (RatFunc k) n) :=
  residueAt_eq_dvr p n

/-- Normalization includes degree one and its empty degree-zero symbol. -/
theorem finite_degree_one (p : k[X]) [Fact (Irreducible p)] :
    zeroEquiv (AdjoinRoot p) (residueAt p 0
      (symbol (Fin.snoc Fin.elim0 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)))) =
      1 := by
  have h := residueAt_polynomial_units p 0 Fin.elim0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)
  have he : (fun i : Fin 0 => polynomialUnit (Fin.elim0 i) (Fin.elim0 i)) =
      (Fin.elim0 : SymbolTuple (RatFunc k) 0) := Subsingleton.elim _ _
  rw [he] at h
  simpa only [zeroEquiv_symbol] using congrArg (zeroEquiv (AdjoinRoot p)) h

/-- The all-degree last-slot finite normalization has no hidden even-degree restriction. -/
theorem finite_last_slot (p : k[X]) [Fact (Irreducible p)] (n : ℕ)
    (q : Fin n → k[X]) (hq : ∀ i, q i ≠ 0) (hqp : ∀ i, ¬ p ∣ q i) :
    residueAt p n (symbol (Fin.snoc (fun i => polynomialUnit (q i) (hq i))
      (polynomialUnit p (Fact.out : Irreducible p).ne_zero))) =
      symbol (fun i => quotientUnit p (q i) (hqp i)) :=
  residueAt_polynomial_units p n q hq hqp

/-- Specialization uses the literal quotient polynomial classes. -/
theorem literal_specialization (p : k[X]) [Fact (Irreducible p)] (n : ℕ)
    (q : Fin n → k[X]) (hq : ∀ i, q i ≠ 0) (hqp : ∀ i, ¬ p ∣ q i) :
    specializeAt p n (symbol (fun i => polynomialUnit (q i) (hq i))) =
      symbol (fun i => quotientUnit p (q i) (hqp i)) :=
  specializeAt_polynomial_units p n q hq hqp

/-- Arbitrary rational symbols use a linear-size divisor-union support bound. -/
theorem actual_support (n : ℕ) (a : SymbolTuple (RatFunc k) (n + 1)) :
    {p : MonicIrreducible k | residueAt p.val n (symbol a) ≠ 0} ⊆ symbolSupportSet a :=
  residueAt_symbol_support_subset n a

/-- The total residue is an actual dependent finitely supported quotient map. -/
noncomputable def actual_total (n : ℕ) : K (RatFunc k) (n + 1) →ₗ[ℤ]
    Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n := totalResidue n

/-- Its coordinates are the finite residue maps on every class. -/
theorem actual_total_coordinate (n : ℕ) (x : K (RatFunc k) (n + 1))
    (p : MonicIrreducible k) : actual_total k n x p = residueAt p.val n x := rfl

/-- The sign is negative in target degree one, where a first-slot convention would differ. -/
theorem infinity_odd_one (a : SymbolTuple k 1) :
    InfinityResidue.residue k 1
      (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a) (InfinityResidue.variableUnit k))) =
      -symbol a := InfinityResidue.residue_variable k 1 a

/-- The same last-slot negative sign persists in target degree three. -/
theorem infinity_odd_three (a : SymbolTuple k 3) :
    InfinityResidue.residue k 3
      (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a) (InfinityResidue.variableUnit k))) =
      -symbol a := InfinityResidue.residue_variable k 3 a

/-- The degree-one infinity formula agrees with negative polynomial degree. -/
theorem infinity_degree_one (p : k[X]) (hp : p ≠ 0) :
    zeroEquiv k (InfinityResidue.residue k 0
      (symbol (Fin.snoc Fin.elim0 (polynomialUnit p hp)))) = -(p.natDegree : ℤ) := by
  have h := InfinityResidue.residue_polynomial_constants k 0 p hp Fin.elim0
  have h' := congrArg (zeroEquiv k) h
  have he : InfinityResidue.constantUnit k ∘ (Fin.elim0 : SymbolTuple k 0) = Fin.elim0 :=
    Subsingleton.elim _ _
  rw [he] at h'
  simpa only [map_smul, zeroEquiv_symbol, smul_eq_mul, mul_one] using h'

/-- Arbitrary nonzero leading coefficients require no monicity hypothesis, also in odd degree. -/
theorem infinity_nonmonic (c : kˣ) (m : ℕ) (a : SymbolTuple k 3) :
    InfinityResidue.residue k 3
      (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a)
        (polynomialUnit (C (c : k) * X ^ m)
          (mul_ne_zero (C_ne_zero.mpr c.ne_zero) (pow_ne_zero _ X_ne_zero))))) =
      -(m : ℤ) • symbol a := by
  simpa only [natDegree_C_mul_X_pow m (c : k) c.ne_zero] using
    InfinityResidue.residue_polynomial_constants k 3 (C (c : k) * X ^ m)
      (mul_ne_zero (C_ne_zero.mpr c.ne_zero) (pow_ne_zero _ X_ne_zero)) a

/-- Nonzero constant polynomials give degree zero and therefore zero residue. -/
theorem infinity_constant_polynomial (n : ℕ) (c : kˣ) (a : SymbolTuple k n) :
    InfinityResidue.residue k n
      (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a)
        (polynomialUnit (C (c : k)) (C_ne_zero.mpr c.ne_zero)))) = 0 := by
  simpa only [natDegree_C, Nat.cast_zero, neg_zero, zero_smul] using
    InfinityResidue.residue_polynomial_constants k n (C (c : k)) (C_ne_zero.mpr c.ne_zero) a

/-- Constants vanish on every quotient class, not only listed symbols. -/
theorem infinity_all_constants (n : ℕ) (x : K k (n + 1)) :
    InfinityResidue.residue k n (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k) x) = 0 :=
  InfinityResidue.residue_constants k n x

end AglibTest.GeneralMilnorPolynomialResidue

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.FieldTheory.RatFuncInversion,
    `Aglib.FieldTheory.RatFuncReverse,
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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorPolynomialResidue]
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
  logInfo m!"Checked {names.size} actual polynomial residue and general Milnor declarations: \
    standard axioms only."
