/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Original Ext classes detected by finite coproduct source maps

The cofan and every component arrow are supplied literally. Its colimit
property gives a comparison with a finite biproduct, and the original Ext
precomposition along its component maps is jointly injective.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace CategoryTheory.Abelian.Ext
universe u v e r
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]

/-- A finite actual coproduct detects zero by its original source inclusions. -/
theorem eq_zero_of_finite_cofan {ι : Type r} [Finite ι] (D : ι → C)
    (c : Cofan D) (hc : IsColimit c) (Y : C) (q : ℕ) (x : Ext c.pt Y q)
    (hx : ∀ i, (Ext.mk₀ (c.inj i)).comp x (Nat.zero_add q) = 0) : x = 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  let : HasCoproduct D := ⟨⟨c, hc⟩⟩
  let : HasBiproduct D := HasBiproduct.of_hasCoproduct D
  let E : (⨁ D) ≅ c.pt := (biproduct.isColimit D).coconePointUniqueUpToIso hc
  have hE (i : ι) : biproduct.ι D i ≫ E.hom = c.inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (biproduct.isColimit D) hc (Discrete.mk i)
  let y : Ext (⨁ D) Y q := (Ext.mk₀ E.hom).comp x (Nat.zero_add q)
  have hy : y = 0 := by
    apply (Ext.biproductAddEquiv (biproduct.isBilimit D) Y q).injective
    funext i
    change (Ext.mk₀ (biproduct.ι D i)).comp y (Nat.zero_add q) =
      (Ext.mk₀ (biproduct.ι D i)).comp 0 (Nat.zero_add q)
    dsimp only [y]
    rw [Ext.mk₀_comp_mk₀_assoc, hE, hx, Ext.comp_zero]
  have hz := congrArg (fun z : Ext (⨁ D) Y q =>
    (Ext.mk₀ E.inv).comp z (Nat.zero_add q)) hy
  simpa only [y, Ext.mk₀_comp_mk₀_assoc, E.inv_hom_id, Ext.mk₀_id_comp,
    Ext.comp_zero] using hz

end CategoryTheory.Abelian.Ext
