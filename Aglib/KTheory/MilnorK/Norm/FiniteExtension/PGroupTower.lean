/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.PrimeTower
public import Aglib.FieldTheory.PGroupNormalSubfieldEmbedding

/-!
# Actual finite norm towers in a p-group lower ambient

Induction on the degree of the actual lower field uses a constructed normal
prime-degree subfield and the proved prime tower. The upper field need not
embed in the p-group ambient. No tower statement is assumed as input.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u

/-- Actual finite-extension norm transitivity when the lower field embeds into
a finite Galois p-group extension. The upper extension is arbitrary finite. -/
theorem finiteExtensionNorm_tower_of_pGroup
    {k L E Ω : Type u} [Field k] [CharZero k] [Field L] [CharZero L]
    [Field E] [Field Ω] [Algebra k L] [Algebra L E] [Algebra k E]
    [IsScalarTower k L E] [Algebra k Ω]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω)) (g : L →ₐ[k] Ω)
    (n : ℕ) (x : K E n) :
    finiteExtensionNorm k E n x = finiteExtensionNorm k L n (finiteExtensionNorm L E n x) := by
  have main : ∀ d : ℕ, ∀ (A B C M : Type u)
      [Field A] [CharZero A] [Field B] [CharZero B] [Field C] [Field M]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra A M]
      [FiniteDimensional A B] [FiniteDimensional B C] [FiniteDimensional A C]
      [FiniteDimensional A M] [IsGalois A M],
      IsPGroup ℓ (M ≃ₐ[A] M) → (B →ₐ[A] M) → Module.finrank A B = d →
      ∀ y : K C n, finiteExtensionNorm A C n y =
        finiteExtensionNorm A B n (finiteExtensionNorm B C n y) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A B C M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM gB hdim y
      by_cases hd : Module.finrank A B = 1
      · exact finiteExtensionNorm_tower_degree_one B C hd n y
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
      let : FiniteDimensional R C := FiniteDimensional.trans R B C
      let : FiniteDimensional R M := FiniteDimensional.right A R M
      let : IsGalois R M := IsGalois.tower_top_of_isGalois A R M
      have hMR : IsPGroup ℓ (M ≃ₐ[R] M) :=
        hM.of_injective (AlgEquiv.restrictScalarsHom A)
          (AlgEquiv.restrictScalarsHom_injective A)
      have hrec := ih (Module.finrank R B) (hdim ▸ hdrop) R B C M hMR
        (IsScalarTower.toAlgHom R B M) rfl y
      have hprime : (Module.finrank A R).Prime := hdegree ▸ (Fact.out : ℓ.Prime)
      rw [finiteExtensionNorm_tower_prime R C hprime n y, hrec,
        ← finiteExtensionNorm_tower_prime R B hprime n]
  exact main (Module.finrank k L) k L E Ω hG g rfl x

end MilnorK
