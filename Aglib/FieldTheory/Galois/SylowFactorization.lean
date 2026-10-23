/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.FiniteAction
public import Aglib.FieldTheory.Galois.Sylow

/-! # Prime-to-p intermediate fields with p-group monodromy image

A continuous discrete homomorphism of the original Galois group factors
through a genuine finite Galois extension. Mapping its Sylow fixed field into
the same ambient field gives an actual prime-to-p extension. Its fixing
subgroup has p-group image under the original homomorphism.
-/

@[expose] public noncomputable section

namespace InfiniteGalois

universe u v w

/-- A genuine finite prime-to-p intermediate field makes the original
continuous discrete monodromy image a p-group. The ambient Galois group
itself is not assumed to be an abstract p-group. -/
theorem exists_primeTo_intermediateField_isPGroup_image
    {E : Type u} {Ω : Type v} [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω]
    {G : Type w} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    {p : ℕ} [Fact p.Prime] (ρ : (Ω ≃ₐ[E] Ω) →* G) (hρ : Continuous ρ) :
    ∃ M : IntermediateField E Ω, FiniteDimensional E M ∧
      (Module.finrank E M).Coprime p ∧
      IsPGroup p (ρ.comp M.fixingSubgroup.subtype).range := by
  obtain ⟨L, ρL, hL⟩ := exists_finiteGalois_factorization ρ hρ
  let P : Sylow p (L ≃ₐ[E] L) := Classical.choice inferInstance
  let N := IntermediateField.fixedField (P : Subgroup (L ≃ₐ[E] L))
  let M : IntermediateField E Ω := N.map L.val
  let e : N ≃ₐ[E] M := N.equivMap L.val
  let : FiniteDimensional E M := LinearEquiv.finiteDimensional e.toLinearEquiv
  have hdegree : (Module.finrank E M).Coprime p := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact IntermediateField.finrank_fixedField_sylow_coprime P
  have hfix : M.fixingSubgroup =
      (P : Subgroup (L ≃ₐ[E] L)).comap (AlgEquiv.restrictNormalHom L) := by
    change (N.map (IsScalarTower.toAlgHom E L Ω)).fixingSubgroup = _
    rw [IntermediateField.map_fixingSubgroup (E' := Ω)]
    exact congrArg (fun H => H.comap (AlgEquiv.restrictNormalHom (K₁ := Ω) L))
      (IntermediateField.fixingSubgroup_fixedField (P : Subgroup (L ≃ₐ[E] L)))
  refine ⟨M, inferInstance, hdegree, ?_⟩
  rintro ⟨g, σ, rfl⟩
  have hσ : (σ : Ω ≃ₐ[E] Ω).restrictNormal L ∈ P := by
    exact (congrArg (fun H : Subgroup (Ω ≃ₐ[E] Ω) =>
      (σ : Ω ≃ₐ[E] Ω) ∈ H) hfix).mp σ.property
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨(σ : Ω ≃ₐ[E] Ω).restrictNormal L, hσ⟩
  refine ⟨n, Subtype.ext ?_⟩
  change ρ (σ : Ω ≃ₐ[E] Ω) ^ p ^ n = 1
  rw [← hL (σ : Ω ≃ₐ[E] Ω), ← map_pow]
  have hpow : (σ : Ω ≃ₐ[E] Ω).restrictNormal L ^ p ^ n = 1 :=
    congrArg Subtype.val hn
  rw [hpow, map_one]

end InfiniteGalois
