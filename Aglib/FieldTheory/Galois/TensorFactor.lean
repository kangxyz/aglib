/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.GroupTheory.Coset.Card

/-! # Actual field factors of a base-changed finite Galois extension

A specified surjection from the original tensor product determines the original
embedding of the old field into its selected factor. A separable splitting
polynomial proves that this same factor is Galois. Native normal restriction
embeds its automorphism group in the original Galois group, retaining the
embedding equation. No target Galois structure or replacement factor is assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u v w z

section Algebras

variable {K : Type u} {L : Type v} {K' : Type w} {M : Type z}
  [CommRing K] [CommRing L] [CommRing K'] [CommRing M]
  [Algebra K L] [Algebra K K'] [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
  (φ : K' ⊗[K] L →ₐ[K'] M)

/-- The original old-field inclusion into a specified tensor factor. -/
def factorEmbedding : L →ₐ[K] M :=
  (φ.restrictScalars K).comp includeRight

/-- The selected factor map retains multiplication of its two original factors. -/
theorem factor_tmul (a : K') (b : L) :
    φ (a ⊗ₜ[K] b) = algebraMap K' M a * factorEmbedding φ b := by
  have he : a ⊗ₜ[K] b =
      algebraMap K' (K' ⊗[K] L) a * (1 ⊗ₜ[K] b) := by
    simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      tmul_mul_tmul, mul_one, one_mul]
  rw [he, map_mul, φ.commutes]
  rfl

/-- Surjectivity of the original factor map gives generation by the unchanged
old-field image over the new coefficient field. -/
theorem factor_adjoin_eq_top (hφ : Function.Surjective φ) :
    Algebra.adjoin K' (Set.range (factorEmbedding φ)) = ⊤ := by
  have hmem (x : K' ⊗[K] L) :
      φ x ∈ Algebra.adjoin K' (Set.range (factorEmbedding φ)) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
        rw [factor_tmul]
        exact (Algebra.adjoin K' (Set.range (factorEmbedding φ))).mul_mem
          (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ⟨b, rfl⟩)
    | add a b ha hb =>
        simpa only [map_add] using
          (Algebra.adjoin K' (Set.range (factorEmbedding φ))).add_mem ha hb
  apply top_unique
  intro x _
  obtain ⟨x, rfl⟩ := hφ x
  exact hmem x

end Algebras

section Fields

variable {K : Type u} {L : Type v} {K' : Type w} {M : Type z}
  [Field K] [Field L] [Field K'] [Field M]
  [Algebra K L] [Algebra K K'] [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
  (φ : K' ⊗[K] L →ₐ[K'] M)

/-- A field factor of the actual base change of a finite Galois extension is
Galois over the new field, proved from the original splitting polynomial. -/
theorem isGalois_factor [FiniteDimensional K L] [IsGalois K L]
    (hφ : Function.Surjective φ) : IsGalois K' M := by
  obtain ⟨p, hp, hpL⟩ := IsGalois.is_separable_splitting_field K L
  let : p.IsSplittingField K L := hpL
  have hsplit : (p.map (algebraMap K M)).Splits := by
    have h := (Polynomial.IsSplittingField.splits L p).map (factorEmbedding φ).toRingHom
    have hcomp : (factorEmbedding φ).toRingHom.comp (algebraMap K L) =
        algebraMap K M := RingHom.ext (factorEmbedding φ).commutes
    rwa [Polynomial.map_map, hcomp] at h
  have hgen : Algebra.adjoin K' (p.rootSet M) = ⊤ := by
    apply top_unique
    rw [← factor_adjoin_eq_top φ hφ]
    apply Algebra.adjoin_le
    have hrange := Polynomial.IsSplittingField.adjoin_rootSet_eq_range L p (factorEmbedding φ)
    have hle : (factorEmbedding φ).range ≤
        (Algebra.adjoin K' (p.rootSet M)).restrictScalars K := by
      rw [← hrange]
      apply Algebra.adjoin_le
      intro x hx
      change x ∈ Algebra.adjoin K' (p.rootSet M)
      exact Algebra.subset_adjoin (R := K') hx
    intro x hx
    exact hle hx
  let : (p.map (algebraMap K K')).IsSplittingField K' M := by
    constructor
    · simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K K' M] using hsplit
    · simpa only [Polynomial.rootSet_map] using hgen
  exact IsGalois.of_separable_splitting_field (p := p.map (algebraMap K K')) hp.map

variable [Normal K L]

/-- Restrict automorphisms of the actual selected factor to the embedded
original normal field. Normality stabilizes that image; no projection to the
old field is chosen or assumed. -/
def factorRestriction : (M ≃ₐ[K'] M) →* (L ≃ₐ[K] L) := by
  letI : Algebra L M := (factorEmbedding φ).toRingHom.toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq
    (fun r => (factorEmbedding φ).commutes r |>.symm)
  exact (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)

/-- Native normal restriction keeps the exact original embedding equation. -/
theorem factorRestriction_commutes (σ : M ≃ₐ[K'] M) (x : L) :
    factorEmbedding φ (factorRestriction φ σ x) = σ (factorEmbedding φ x) := by
  let : Algebra L M := (factorEmbedding φ).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq
    (fun r => (factorEmbedding φ).commutes r |>.symm)
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L x

/-- An automorphism fixing both original tensor factors fixes the selected
factor, by surjectivity of its original tensor map. -/
theorem factorRestriction_injective (hφ : Function.Surjective φ) :
    Function.Injective (factorRestriction φ) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := hφ x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      rw [factor_tmul, map_mul, map_mul, σ.commutes, τ.commutes,
        ← factorRestriction_commutes, ← factorRestriction_commutes, hστ]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The original selected-factor automorphism order divides the original
normal-extension automorphism order, through actual normal restriction. -/
theorem factor_card_aut_dvd (hφ : Function.Surjective φ) :
    Nat.card (M ≃ₐ[K'] M) ∣ Nat.card (L ≃ₐ[K] L) :=
  Subgroup.card_dvd_of_injective (factorRestriction φ) (factorRestriction_injective φ hφ)

end Fields

end Algebra.TensorProduct
