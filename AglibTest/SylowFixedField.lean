/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.SylowFixedField
import Lean.Util.CollectAxioms

/-! Direct consumers of finite prime-power root descent and actual Sylow fixed
fields. The explicit splitting field, zero/constant cases, and simultaneous
finite-family endpoint are checked with complete proof-body axiom inspection. -/

open Polynomial IntermediateField

namespace AglibTest.SylowFixedField

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- Roots descend in an actual prime-power extension, without a Galois hypothesis. -/
theorem actual_root_descent (S : IntermediateField k M) [FiniteDimensional S M]
    (p r : ℕ) (hp : p.Prime) (hdegree : Module.finrank S M = p ^ r)
    (q : k[X]) (hq : q ≠ 0) (hqd : q.natDegree < p) (x : M) (hx : aeval x q = 0) :
    x ∈ S :=
  mem_of_small_root_of_finrank_prime_pow S p r hp hdegree q hq hqd x hx

/-- Polynomial splitting descends with its genuine prime-power field degree. -/
theorem actual_prime_power_splitting (S : IntermediateField k M)
    [FiniteDimensional S M] (p r : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank S M = p ^ r) (q : k[X]) (hqd : q.natDegree < p)
    (hq : (q.map (algebraMap k M)).Splits) : (q.map (algebraMap k S)).Splits :=
  splits_of_small_degree_of_finrank_prime_pow S p r hp hdegree q hqd hq

variable [FiniteDimensional k M] (p : ℕ) [Fact p.Prime]

/-- The overfield degree is an actual prime power, not a degree bound. -/
theorem sylow_power (H : Sylow p (M ≃ₐ[k] M)) :
    ∃ r : ℕ, Module.finrank (fixedField (H : Subgroup (M ≃ₐ[k] M))) M = p ^ r :=
  finrank_over_sylow_fixedField p H

/-- The zero polynomial is expressly included. -/
theorem zero_polynomial (H : Sylow p (M ≃ₐ[k] M)) :
    ((0 : k[X]).map
      (algebraMap k (fixedField (H : Subgroup (M ≃ₐ[k] M))))).Splits :=
  splits_over_sylow_fixedField_of_small_degree p H 0
    (by simpa only [natDegree_zero] using (Fact.out : p.Prime).pos)
    (by simp only [Polynomial.map_zero, Splits.zero])

/-- Nonzero constants, as well as zero constants, cause no degree exception. -/
theorem constant_polynomial (H : Sylow p (M ≃ₐ[k] M)) (c : k) :
    ((C c).map (algebraMap k (fixedField (H : Subgroup (M ≃ₐ[k] M))))).Splits :=
  splits_over_sylow_fixedField_of_small_degree p H (C c)
    (by simpa only [natDegree_C] using (Fact.out : p.Prime).pos)
    (by simp only [Polynomial.map_C, Splits.C])

/-- Actual base-degree coprimality uses the finite Galois hypothesis. -/
theorem actual_coprime_degree [IsGalois k M] (H : Sylow p (M ≃ₐ[k] M)) :
    p.Coprime (Module.finrank k (fixedField (H : Subgroup (M ≃ₐ[k] M)))) :=
  coprime_finrank_sylow_fixedField p H

/-- One actual finite field works for every polynomial in the supplied family. -/
theorem simultaneous_finite_splitting [IsGalois k M]
    (s : Finset k[X]) (hsmall : ∀ q ∈ s, q.natDegree < p)
    (hsplit : ∀ q ∈ s, (q.map (algebraMap k M)).Splits) :
    ∃ S : IntermediateField k M, FiniteDimensional k S ∧
      p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits :=
  exists_coprime_splitting_intermediateField p s hsmall hsplit

end AglibTest.SylowFixedField

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.FieldTheory.SylowFixedField
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.size < 6 then
    throwError "The native source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.SylowFixedField).isPrefixOf name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} native finite Sylow and consumer declarations: \
    standard axioms only."
