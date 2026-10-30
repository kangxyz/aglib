/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Aglib.CategoryTheory.Sites.Torsion.Sheaf

/-! # Internal local torsion of the original constant-ring modules

The property is exactly local torsion of the original additive sheaf.
A positive annihilator of the scalar unit is only a sufficient criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]

private theorem isTorsion_of_sameIso {F G : Sheaf J AddCommGrpCat.{w}}
    (e : F ≅ G) (hG : Sheaf.IsTorsion G) : Sheaf.IsTorsion F := by
  apply Presheaf.IsLocallyTorsion.of_injective hG e.hom.hom
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

section Native

variable [HasWeakSheafify J RingCat.{r}]

/-- The existing local-annihilator condition on the same underlying sheaf. -/
def moduleIsTorsion (M : ModuleSheaf.{u, v, r, w} J Λ) : Prop :=
  Sheaf.IsTorsion ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).obj M)

/-- The original module isomorphism preserves the same local condition. -/
theorem moduleIsTorsion_of_iso {M N : ModuleSheaf.{u, v, r, w} J Λ} (e : M ≅ N)
    (hN : moduleIsTorsion J Λ N) : moduleIsTorsion J Λ M :=
  isTorsion_of_sameIso (J := J)
    ((SheafOfModules.toSheaf.{w} (constantRing J Λ)).mapIso e) hN

end Native

section Valued

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- A positive annihilator of the scalar unit annihilates every actual
module-valued section and hence gives internal local torsion. -/
theorem moduleValuedUnderlying_isTorsion_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    (M : ModuleValuedSheaf.{u, v, r, w} J Λ) :
    Sheaf.IsTorsion
      ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj M) := by
  have hcast : (N : Λ) = 0 := by simpa only [nsmul_one] using hΛ
  have kill (V : ModuleCat.{w} Λ) (x : V) : N • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul Λ, hcast, zero_smul]
  apply Presheaf.isLocallyTorsion_of_sectionwise
  intro U s
  exact ⟨N, hN, kill (M.obj.obj (op U)) s⟩

variable [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The original coefficient equivalence transfers this sufficient criterion
to the same native ringed module sheaf. -/
theorem moduleIsTorsion_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    (M : ModuleSheaf.{u, v, r, w} J Λ) : moduleIsTorsion J Λ M := by
  have ht := moduleValuedUnderlying_isTorsion_of_nsmul_one_eq_zero J Λ N hN hΛ
    ((moduleSheafEquivalence J Λ).inverse.obj M)
  exact isTorsion_of_sameIso (J := J)
    ((moduleSheafInverseUnderlyingIso J Λ).app M).symm ht

end Valued

end ModuleCat.Sheaf.ConstantRing
