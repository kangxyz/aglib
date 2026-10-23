/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Profinite

/-! # Factoring a discrete Galois action through an actual finite extension

The open kernel contains the fixing subgroup of a genuine finite Galois
intermediate field. Surjective restriction then descends the original group
homomorphism, retaining its exact evaluation on every ambient automorphism.
-/

@[expose] public noncomputable section

open scoped Topology

namespace InfiniteGalois

universe u v w

/-- Every continuous homomorphism from the native Galois group to a discrete
group factors through the Galois group of an actual finite intermediate field. -/
theorem exists_finiteGalois_factorization
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    {G : Type w} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ρ : (Ω ≃ₐ[K] Ω) →* G) (hρ : Continuous ρ) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      ∃ ρL : (L ≃ₐ[K] L) →* G,
        ∀ σ : Ω ≃ₐ[K] Ω, ρL (σ.restrictNormal L) = ρ σ := by
  have hker : (ρ.ker : Set (Ω ≃ₐ[K] Ω)) ∈ 𝓝 1 := by
    exact ((isOpen_discrete ({1} : Set G)).preimage hρ).mem_nhds ρ.map_one
  obtain ⟨L, hL⟩ :=
    (krullTopology_mem_nhds_one_iff_of_isGalois (ρ.ker : Set (Ω ≃ₐ[K] Ω))).mp hker
  let f : (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  have hf : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω
  have hle : f.ker ≤ ρ.ker := by
    change (AlgEquiv.restrictNormalHom L).ker ≤ ρ.ker
    rw [IntermediateField.restrictNormalHom_ker]
    exact hL
  refine ⟨L, f.liftOfSurjective hf ⟨ρ, hle⟩, ?_⟩
  intro σ
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

end InfiniteGalois
