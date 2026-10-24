/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Identifying the original underlying mate from its unit equation

A specified inverse-image comparison and a specified direct-image transformation
are mates as soon as their original units agree. The proof keeps all functors
opaque and uses the native adjunction hom-equivalence, so concrete coefficient
comparisons need not unfold their sheafification constructions.
-/

@[expose] public section

namespace CategoryTheory

universe uA vA uB vB uC vC uD vD

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The original unit equation identifies the mate of the inverse specified
comparison, without requiring the direct-image transformation to be invertible. -/
theorem mateEquiv_inv_natTrans_eq_of_unit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₁ ⋙ V ≅ U ⋙ L₂) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    (h : ∀ M, U.map (adj₁.unit.app M) ≫ d.app (L₁.obj M) ≫
      R₂.map (e.hom.app M) = adj₂.unit.app (U.obj M)) :
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d := by
  let β := TwoSquare.mk _ _ _ _ d
  have hs : (mateEquiv adj₁ adj₂).symm β = TwoSquare.mk _ _ _ _ e.inv := by
    apply TwoSquare.ext
    intro M
    apply (adj₂.homEquiv _ _).injective
    change adj₂.unit.app (U.obj M) ≫
        R₂.map (((mateEquiv adj₁ adj₂).symm β).natTrans.app M) =
      adj₂.unit.app (U.obj M) ≫ R₂.map (e.inv.app M)
    have hu : U.map (adj₁.unit.app M) ≫ d.app (L₁.obj M) =
        adj₂.unit.app (U.obj M) ≫
          R₂.map (((mateEquiv adj₁ adj₂).symm β).natTrans.app M) :=
      unit_mateEquiv_symm adj₁ adj₂ β M
    rw [← hu, ← h M]
    simp only [Category.assoc, ← R₂.map_comp, Iso.hom_inv_id_app]
    exact congrArg (fun k => U.map (adj₁.unit.app M) ≫ k)
      ((congrArg (fun k => d.app (L₁.obj M) ≫ k)
        (R₂.map_id ((L₁ ⋙ V).obj M))).trans
          (Category.comp_id (d.app (L₁.obj M)))).symm
  have hm := congrArg (fun α => (mateEquiv adj₁ adj₂ α).natTrans) hs
  simpa only [Equiv.apply_symm_apply] using hm.symm

end CategoryTheory
