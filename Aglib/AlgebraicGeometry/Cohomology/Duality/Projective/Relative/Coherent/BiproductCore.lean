/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Componentwise bijectivity for the coefficient biproduct

The native Ext biproduct equivalence and the mapped target bilimit identify a
natural comparison on a finite biproduct from its original projection squares.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u₁ v₁ u₂ v₂ u₃ v₃ w j

namespace CategoryTheory.Abelian.Ext

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- Natural comparison maps into a finite coefficient biproduct are bijective
whenever each original component is bijective. -/
theorem bijective_comparison_biproduct
    (W : C ⥤ D) [W.Additive] (G : C ⥤ E) [G.Additive]
    {J : Type j} [Finite J] (N : J → C) [HasBiproduct N]
    (M : D) (K : E) (q : ℕ)
    (φ : Ext.{w} M (W.obj (biproduct N)) q →+ (K ⟶ G.obj (biproduct N)))
    (φj : ∀ i, Ext.{w} M (W.obj (N i)) q →+ (K ⟶ G.obj (N i)))
    (hφ : ∀ i x, φj i (x.comp (Ext.mk₀ (W.map (biproduct.π N i))) (Nat.add_zero q)) =
      φ x ≫ G.map (biproduct.π N i))
    (hj : ∀ i, Function.Bijective (φj i)) : Function.Bijective φ := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have hW : (W.mapBicone (biproduct.bicone N)).IsBilimit :=
    isBilimitOfTotal _ (by
      simp_rw [W.mapBicone_π, W.mapBicone_ι, ← W.map_comp]
      erw [← W.map_sum, ← W.map_id, IsBilimit.total (biproduct.isBilimit N)])
  have hG : (G.mapBicone (biproduct.bicone N)).IsBilimit :=
    isBilimitOfTotal _ (by
      simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
      erw [← G.map_sum, ← G.map_id, IsBilimit.total (biproduct.isBilimit N)])
  let A := Ext.addEquivBiproduct M hW q
  constructor
  · intro x y hxy
    apply A.injective
    funext i
    apply (hj i).injective
    change φj i (x.comp (Ext.mk₀ (W.map (biproduct.π N i))) (Nat.add_zero q)) =
      φj i (y.comp (Ext.mk₀ (W.map (biproduct.π N i))) (Nat.add_zero q))
    rw [hφ, hφ, hxy]
  · intro y
    choose x hx using fun i => (hj i).surjective (y ≫ G.map (biproduct.π N i))
    refine ⟨A.symm x, ?_⟩
    apply hG.isLimit.hom_ext
    rintro ⟨i⟩
    change φ (A.symm x) ≫ G.map (biproduct.π N i) = y ≫ G.map (biproduct.π N i)
    rw [← hφ]
    have he := congrFun (A.apply_symm_apply x) i
    change (A.symm x).comp (Ext.mk₀ (W.map (biproduct.π N i))) (Nat.add_zero q) = x i at he
    rw [he, hx]

end CategoryTheory.Abelian.Ext
