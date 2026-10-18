/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.FieldTheory.PGroupNormalSubfield
import Lean.Util.CollectAxioms

/-! Direct consumers of the actual fixed field and strict induction step. -/

namespace AglibTest.PGroupNormalSubfield

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The chosen subgroup contains the original fixing subgroup, retaining
the actual inclusion of its normal prime-degree fixed field in the input. -/
theorem actual_fixed_field (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ J : Subgroup (Ω ≃ₐ[k] Ω), E.fixingSubgroup ≤ J ∧ J.Normal ∧ J.index = p ∧
      IntermediateField.fixedField J ≤ E ∧
      Module.finrank k (IntermediateField.fixedField J) = p ∧
      Normal k (IntermediateField.fixedField J) :=
  IntermediateField.exists_normal_prime_fixedField p hG E hE

/-- The induction field is a literal intermediate field of the original E. -/
theorem actual_prime_subfield (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ L : IntermediateField k E, Normal k L ∧ Module.finrank k L = p ∧
      Module.finrank L E < Module.finrank k E :=
  IntermediateField.exists_normal_prime_subfield_of_isPGroup p hG E hE

/-- A strong-induction hypothesis can be invoked on the actual upper
extension, while the lower extension is normal of prime degree. -/
theorem induction_step (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥)
    (P : ℕ → Prop) (hP : ∀ d < Module.finrank k E, P d) :
    ∃ L : IntermediateField k E, Normal k L ∧ Module.finrank k L = p ∧
      P (Module.finrank L E) := by
  obtain ⟨L, hL, hdegree, hlt⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_isPGroup p hG E hE
  exact ⟨L, hL, hdegree, hP _ hlt⟩

end AglibTest.PGroupNormalSubfield

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModule := `Aglib.FieldTheory.PGroupNormalSubfield
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == sourceModule then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  if names.isEmpty then
    throwError "The actual p-group prime-subfield source declarations are missing from this audit"
  names := env.constants.foldStage2 (fun names name _ =>
    if (`AglibTest.PGroupNormalSubfield).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} p-group prime-subfield declarations: standard axioms only."
