/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.PGroupNormalPrimePresentation
import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeSubfieldInduction
import Lean.Util.CollectAxioms

/-! Direct consumers retain the original field and feed the actual norm induction step. -/

namespace AglibTest.PGroupNormalPrimePresentation

open Polynomial MilnorK
open PolynomialNorm PolynomialResidue

variable {k H Ω : Type*} [Field k] [Field H] [Field Ω]
  [Algebra k H] [Algebra k Ω] [FiniteDimensional k H]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The bare intermediate-field conclusion has no characteristic hypothesis. -/
theorem original_field_subfield (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : H →ₐ[k] Ω)
    (hH : 1 < Module.finrank k H) :
    ∃ L : IntermediateField k H, Normal k L ∧ Module.finrank k L = p ∧
      Module.finrank L H < Module.finrank k H :=
  IntermediateField.exists_normal_prime_subfield_of_embedding p hG g hH

/-- The constructed polynomial has exactly the specified prime degree and
its actual root field maps to H, not just to the ambient field. -/
theorem original_field_presentation [CharZero k] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : H →ₐ[k] Ω)
    (hH : 1 < Module.finrank k H) :
    ∃ r : MonicIrreducible k, Normal k (AdjoinRoot r.val) ∧ r.val.natDegree = p ∧
      Nonempty (AdjoinRoot r.val →ₐ[k] H) :=
  exists_normal_prime_presentation_of_isPGroup_embedding p hG g hH

/-- The presentation feeds the proved prime-subfield norm induction, with
the induction premise still confined to strictly smaller degrees. -/
theorem actual_norm_induction_input [CharZero k] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (h₁ h₂ : MonicIrreducible k)
    (g : AdjoinRoot h₁.val →ₐ[k] Ω) (hdegree : 1 < h₁.val.natDegree)
    (e : AdjoinRoot h₁.val ≃ₐ[k] AdjoinRoot h₂.val) (n : ℕ)
    (ih : ∀ (r : MonicIrreducible k), Normal k (AdjoinRoot r.val) →
      r.val.natDegree = p → ∀ (a b : MonicIrreducible (AdjoinRoot r.val)),
        a.val.natDegree < h₁.val.natDegree →
        ∀ (ε : AdjoinRoot a.val ≃ₐ[AdjoinRoot r.val] AdjoinRoot b.val)
          (y : K (AdjoinRoot a.val) n),
          polynomialNorm n b (map n ε.toRingHom y) = polynomialNorm n a y)
    (x : K (AdjoinRoot h₁.val) n) :
    polynomialNorm n h₂ (map n e.toRingHom x) = polynomialNorm n h₁ x := by
  let : FiniteDimensional k (AdjoinRoot h₁.val) :=
    (AdjoinRoot.powerBasis h₁.property.2.ne_zero).finite
  have hdim : 1 < Module.finrank k (AdjoinRoot h₁.val) := by
    rwa [(AdjoinRoot.powerBasis h₁.property.2.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  obtain ⟨r, hnormal, hr, ⟨f⟩⟩ :=
    exists_normal_prime_presentation_of_isPGroup_embedding p hG g hdim
  let : Normal k (AdjoinRoot r.val) := hnormal
  exact polynomialNorm_map_algEquiv_of_prime_subfield_of_lower_degrees r
    (hr ▸ (Fact.out : p.Prime)) h₁ h₂ e f n (ih r hnormal hr) x

end AglibTest.PGroupNormalPrimePresentation

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let sourceModules := #[`Aglib.FieldTheory.PGroupNormalSubfieldEmbedding,
    `Aglib.KTheory.MilnorK.PGroupNormalPrimePresentation]
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
    if (`AglibTest.PGroupNormalPrimePresentation).isPrefixOf name then
      names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} p-group prime-presentation declarations: standard axioms only."
