/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.CoprimeIrreducibility
import Aglib.FieldTheory.FiniteCoprimeSplitting
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Lean.Util.CollectAxioms

/-! Direct consumers of genuine coprime-degree irreducibility and finite
prime-to-prime splitting. Both native modules and every consumer receive a
checked-proof-body axiom audit. -/

open Polynomial IntermediateField

namespace AglibTest.FiniteCoprimeSplitting

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]

/-- No perfectness or separability is needed for this irreducibility transport. -/
theorem actual_irreducibility (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr hcop

/-- Every actual irreducible factor retains the original degree as a divisor. -/
theorem actual_factor_degree (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L))
    (q : L[X]) (hq : Irreducible q) (hdiv : q ∣ p.map (algebraMap k L)) :
    p.natDegree ∣ q.natDegree :=
  natDegree_dvd_of_irreducible_factor_of_coprime hp hirr hcop hq hdiv

/-- The actual finite extension is irrelevant for a linear polynomial. -/
theorem linear_polynomial (a : k) :
    Irreducible ((X - C a).map (algebraMap k L)) :=
  (monic_X_sub_C a).irreducible_map_of_natDegree_coprime (irreducible_X_sub_C a)
    (by rw [natDegree_X_sub_C]; exact Nat.coprime_one_left _)

/-- For prime-degree polynomials the ordinary prime-to-prime condition suffices. -/
theorem prime_degree (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hprime : p.natDegree.Prime) (hdegree : ¬ p.natDegree ∣ Module.finrank k L) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr (hprime.coprime_iff_not_dvd.mpr hdegree)

/-- Arbitrary purely inseparable finite extensions are allowed in the leaf.
No perfect-base hypothesis or separability instance is present. -/
theorem purely_inseparable_coefficients [IsPurelyInseparable k L]
    (p : k[X]) (hp : p.Monic) (hirr : Irreducible p)
    (hcop : p.natDegree.Coprime (Module.finrank k L)) :
    Irreducible (p.map (algebraMap k L)) :=
  hp.irreducible_map_of_natDegree_coprime hirr hcop

/-- Repeated polynomial factors are permitted; the polynomial need not be separable. -/
theorem repeated_linear_factor [PerfectField k] (p d : ℕ) [Fact p.Prime]
    (a : k) (hd : d < p) :
    ∃ S : IntermediateField k (∏ q ∈ ({(X - C a) ^ d} : Finset k[X]), q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      (((X - C a) ^ d).map (algebraMap k S)).Splits := by
  classical
  obtain ⟨S, hfd, hcop, hsplit⟩ := exists_coprime_splitting_field_of_finset p
    ({(X - C a) ^ d} : Finset k[X])
    (by simpa only [Finset.mem_singleton, forall_eq] using pow_ne_zero d (X_sub_C_ne_zero a))
    (by simpa only [Finset.mem_singleton, forall_eq, natDegree_pow,
      natDegree_X_sub_C, Nat.mul_one] using hd)
  exact ⟨S, hfd, hcop, hsplit _ (Finset.mem_singleton_self _)⟩

/-- The empty finite witness set is allowed; its product is one. -/
theorem empty_witnesses [PerfectField k] (p : ℕ) [Fact p.Prime] :
    ∃ S : IntermediateField k (∏ q ∈ (∅ : Finset k[X]), q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) := by
  obtain ⟨S, hfd, hcop, _⟩ := exists_coprime_splitting_field_of_finset (k := k) p ∅
    (by simp) (by simp)
  exact ⟨S, hfd, hcop⟩

/-- Perfect fields of positive characteristic are included in the splitting result. -/
theorem characteristic_two (s : Finset (ZMod 2)[X]) (hne : ∀ q ∈ s, q ≠ 0)
    (hsmall : ∀ q ∈ s, q.natDegree < 3) :
    ∃ S : IntermediateField (ZMod 2) (∏ q ∈ s, q).SplittingField,
      FiniteDimensional (ZMod 2) S ∧ (3 : ℕ).Coprime (Module.finrank (ZMod 2) S) ∧
      ∀ q ∈ s, (q.map (algebraMap (ZMod 2) S)).Splits :=
  exists_coprime_splitting_field_of_finset 3 s hne hsmall

/-- Characteristic zero supplies precisely the perfect-base hypothesis. -/
theorem characteristic_zero [CharZero k] (p : ℕ) [Fact p.Prime]
    (s : Finset k[X]) (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < p) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits :=
  exists_coprime_splitting_field_of_finset p s hne hsmall

end AglibTest.FiniteCoprimeSplitting

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModules := #[`Aglib.FieldTheory.CoprimeIrreducibility,
    `Aglib.FieldTheory.FiniteCoprimeSplitting]
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if sourceModules.contains env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 3 then
    throwError "The native source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.FiniteCoprimeSplitting).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} native finite coprime and consumer declarations: \
    standard axioms only."
