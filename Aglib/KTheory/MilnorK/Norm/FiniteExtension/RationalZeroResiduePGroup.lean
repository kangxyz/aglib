/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalZeroResiduePrime
public import Aglib.FieldTheory.PGroupNormalSubfieldEmbedding

/-!
# Normalized rational X-residue compatibility over a p-group ambient

Degree induction uses actual normal-prime intermediate fields, the proved
prime X-square, and general rational/finite norm transitivity. No residue
compatibility hypothesis is retained by the resulting p-group theorem.
-/

@[expose] public noncomputable section

namespace MilnorK

open scoped RatFunc

attribute [local instance] Polynomial.algebra zeroRationalFinite

universe u

/-- Every actual finite extension embedded in a finite Galois p-group ambient
satisfies the normalized rational X-square in every Milnor degree. -/
theorem rationalZeroResidue_finiteExtensionNorm_of_pGroup
    {k E Ω : Type u} [Field k] [CharZero k] [Field E] [CharZero E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [FiniteDimensional k E]
    [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω)) (g : E →ₐ[k] Ω)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    rationalZeroResidue k n
      (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
        finiteExtensionNorm k E n (rationalZeroResidue E n x) := by
  have main : ∀ d : ℕ, ∀ (A B M : Type u)
      [Field A] [CharZero A] [Field B] [CharZero B] [Field M]
      [Algebra A B] [Algebra A M] [FiniteDimensional A B]
      [FiniteDimensional A M] [IsGalois A M],
      IsPGroup ℓ (M ≃ₐ[A] M) → (B →ₐ[A] M) → Module.finrank A B = d →
      ∀ y : K (RatFunc B) (n + 1),
        rationalZeroResidue A n
          (finiteExtensionNorm (RatFunc A) (RatFunc B) (n + 1) y) =
            finiteExtensionNorm A B n (rationalZeroResidue B n y) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A B M _ _ _ _ _ _ _ _ _ _ hM gB hdim y
      by_cases hd : Module.finrank A B = 1
      · exact rationalZeroResidue_finiteExtensionNorm_degree_one B hd n y
      have hd1 : 1 < Module.finrank A B := by
        have hpos := Module.finrank_pos (R := A) (M := B)
        omega
      obtain ⟨R, hnormal, hdegree, hdrop⟩ :=
        IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hM gB hd1
      let : Normal A R := hnormal
      let : CharZero R := charZero_of_injective_algebraMap (algebraMap A R).injective
      let : Algebra B M := gB.toRingHom.toAlgebra
      let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq' gB.comp_algebraMap.symm
      let : FiniteDimensional R B := FiniteDimensional.right A R B
      let : FiniteDimensional R M := FiniteDimensional.right A R M
      let : IsGalois R M := IsGalois.tower_top_of_isGalois A R M
      have hMR : IsPGroup ℓ (M ≃ₐ[R] M) :=
        hM.of_injective (AlgEquiv.restrictScalarsHom A)
          (AlgEquiv.restrictScalarsHom_injective A)
      have hrec := ih (Module.finrank R B) (hdim ▸ hdrop) R B M hMR
        (IsScalarTower.toAlgHom R B M) rfl y
      have hprime : (Module.finrank A R).Prime := hdegree ▸ (Fact.out : ℓ.Prime)
      rw [finiteExtensionNorm_rational_tower R B (n + 1), LinearMap.comp_apply,
        rationalZeroResidue_finiteExtensionNorm_prime R hprime n, hrec,
        ← finiteExtensionNorm_tower R B n]
  exact main (Module.finrank k E) k E Ω hG g rfl x

end MilnorK
