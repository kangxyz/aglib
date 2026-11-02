/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Full

/-!
# Full scalar forgetting for lifted ZMod coefficients

Every scalar in `ULift (ZMod n)` is an integer cast, so every additive map
between its modules is linear. The original constant-ring coefficient
equivalence transports this fullness to the native ringed-sheaf forgetting
functor on any site with the displayed sheafification hypotheses.
The result includes `n = 0` and is independent of roots of unity.

Sources: Mathlib `Algebra/Module/ZMod.lean`, `map_intCast_smul`;
`ConstantRing/Underlying.lean`, `moduleSheafInverseUnderlyingIso`.
-/

@[expose] public noncomputable section

universe u v r w

open CategoryTheory

namespace ModuleCat

/-- Every additive map between modules over a lifted ZMod ring is linear. -/
theorem uLiftZMod_forget₂_full (n : ℕ) :
    (forget₂ (ModuleCat.{w} (ULift.{r} (ZMod n))) AddCommGrpCat.{w}).Full where
  map_surjective {M N} f := by
    let g : M →+ N := f.hom
    refine ⟨ModuleCat.ofHom { toFun := g, map_add' := g.map_add, map_smul' := fun a m => ?_ },
      rfl⟩
    obtain ⟨z, rfl⟩ : ∃ z : ℤ, (z : ULift.{r} (ZMod n)) = a :=
      ⟨ZMod.cast a.down, ULift.ext _ _
        ((ULift.down_intCast _).trans (ZMod.intCast_zmod_cast a.down))⟩
    simpa using map_intCast_smul g (ULift.{r} (ZMod n)) (ULift.{r} (ZMod n)) z m

namespace Sheaf.ConstantRing

section Annihilation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [HasWeakSheafify J RingCat.{r}]

/-- In sheaves of `ℤ/n`-modules over the constant ring, multiplication by `n` is zero. -/
theorem uLiftZMod_nsmul_id_eq_zero (F : ModuleSheaf.{u, v, r, w} J (ULift.{r} (ZMod n))) :
    n • 𝟙 F = 0 := by
  have hΛ : (n : ULift.{r} (ZMod n)) = 0 := ULift.ext _ _ (by simp)
  apply (SheafOfModules.toSheaf (constantRing J (ULift.{r} (ZMod n)))).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply Sheaf.hom_ext
  ext V x
  have hR : (n : (constantRing J (ULift.{r} (ZMod n))).obj.obj V) = 0 := by
    rw [← map_natCast ((constantRingUnit J (ULift.{r} (ZMod n))).app V).hom n]
    exact (congrArg ((constantRingUnit J (ULift.{r} (ZMod n))).app V).hom hΛ).trans
      (map_zero _)
  have hM : ∀ y : F.val.obj V, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul ((constantRing J (ULift.{r} (ZMod n))).obj.obj V), hR,
      zero_smul]
  exact hM x

end Annihilation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ULift.{r} (ZMod n))) AddCommGrpCat.{w})]

/-- Native scalar forgetting for a constant lifted ZMod ring sheaf is full. -/
theorem uLiftZMod_toSheaf_full :
    (SheafOfModules.toSheaf.{w} (constantRing J (ULift.{r} (ZMod n)))).Full := by
  let : (forget₂ (ModuleCat.{w} (ULift.{r} (ZMod n))) AddCommGrpCat.{w}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  exact Functor.Full.of_iso (moduleSheafInverseUnderlyingIso J (ULift.{r} (ZMod n)))

end Sheaf.ConstantRing

end ModuleCat
