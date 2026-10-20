/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia.Compactness`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`77c301c3b850e70037b1a89d3fbb1027282ff140617f471a4f31c783e704b9ca`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace integralClosure.Inertia.Compactness

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]


/-- Literal residue triviality on one integral element is closed in the actual
Krull topology. The element lies in a finite Galois subextension, so this
condition is the preimage of a subset of its finite discrete Galois group. -/
theorem isClosed_residueCondition (Q : Ideal (integralClosure R Ω))
    (x : integralClosure R Ω) :
    IsClosed {σ : Ω ≃ₐ[K] Ω | σ • x - x ∈ Q} := by
  let L := FiniteGaloisIntermediateField.adjoin K ({(x : Ω)} : Set Ω)
  have hx : (x : Ω) ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  let r : (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let C : Set (Ω ≃ₐ[K] Ω) := {σ | σ • x - x ∈ Q}
  have hsaturated : r ⁻¹' (r '' C) = C := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, he⟩
      have hval := congrArg (fun g : L ≃ₐ[K] L => (g ⟨(x : Ω), hx⟩ : Ω)) he
      have hpoint : τ • x = σ • x := by
        apply Subtype.ext
        change τ (x : Ω) = σ (x : Ω)
        simpa only [r, AlgEquiv.restrictNormalHom_apply] using hval
      change σ • x - x ∈ Q
      rw [← hpoint]
      exact hτ
    · intro hσ
      exact ⟨σ, hσ, rfl⟩
  have hclosed : IsClosed (r ⁻¹' (r '' C)) :=
    (isClosed_discrete _).preimage
      (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)
  rwa [hsaturated] at hclosed

/-- The actual inertia subgroup of the integral closure is closed. No
henselization, finite-level classification, or replacement group is used. -/
theorem isClosed_inertia (Q : Ideal (integralClosure R Ω)) :
    IsClosed (Q.inertia (Ω ≃ₐ[K] Ω) : Set (Ω ≃ₐ[K] Ω)) := by
  have he : (Q.inertia (Ω ≃ₐ[K] Ω) : Set (Ω ≃ₐ[K] Ω)) =
      ⋂ x : integralClosure R Ω, {σ : Ω ≃ₐ[K] Ω | σ • x - x ∈ Q} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, Ideal.mem_inertia]
  rw [he]
  exact isClosed_iInter (isClosed_residueCondition R K Ω Q)

/-- Compactness upgrades finite solvability of literal residue conditions,
with a prescribed finite-field restriction, to an actual inertia lift.

The finite solvability hypothesis is a named remaining input here. It is not
asserted for the DVR automatically by this theorem. -/
theorem exists_inertia_lift_of_finite_conditions
    (Q : Ideal (integralClosure R Ω)) (L : FiniteGaloisIntermediateField K Ω)
    (τ : L ≃ₐ[K] L)
    (hfinite : ∀ s : Finset (integralClosure R Ω),
      ∃ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom L σ = τ ∧
        ∀ x ∈ s, σ • x - x ∈ Q) :
    ∃ σ : Ω ≃ₐ[K] Ω, σ ∈ Q.inertia (Ω ≃ₐ[K] Ω) ∧
      AlgEquiv.restrictNormalHom L σ = τ := by
  let r : (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let C : Set (Ω ≃ₐ[K] Ω) := r ⁻¹' {τ}
  have hcompact : IsCompact C :=
    ((isClosed_singleton : IsClosed ({τ} : Set (L ≃ₐ[K] L))).preimage
      (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)).isCompact
  obtain ⟨σ, hσ⟩ := hcompact.inter_iInter_nonempty
    (fun x : integralClosure R Ω => {σ : Ω ≃ₐ[K] Ω | σ • x - x ∈ Q})
    (isClosed_residueCondition R K Ω Q) (by
      intro s
      obtain ⟨σ, hσ, hs⟩ := hfinite s
      exact ⟨σ, hσ, by simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hs⟩)
  refine ⟨σ, ?_, hσ.1⟩
  rw [Ideal.mem_inertia]
  simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hσ.2

end integralClosure.Inertia.Compactness
