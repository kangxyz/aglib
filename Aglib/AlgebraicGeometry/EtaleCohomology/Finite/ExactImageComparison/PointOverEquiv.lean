/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Actual point fibres through affine isomorphisms and cartesian base change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Transport actual points with their original base triangle through an isomorphism. -/
def pointOverEquivOfIso {C : Type*} [Category* C] {P Z Y S : C}
    (e : Z ≅ Y) (a : Z ⟶ S) (p : Y ⟶ S) (h : e.hom ≫ p = a) (b : P ⟶ S) :
    {q : P ⟶ Z // q ≫ a = b} ≃ {q : P ⟶ Y // q ≫ p = b} where
  toFun q := ⟨q.val ≫ e.hom, by rw [Category.assoc, h]; exact q.property⟩
  invFun q := ⟨q.val ≫ e.inv, by
    rw [← h]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using q.property⟩
  left_inv q := by
    apply Subtype.ext
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv q := by
    apply Subtype.ext
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- The pullback universal property identifies the actual geometric fibres,
not merely their sets of topological supports. -/
def pullbackPointOverEquiv {C : Type*} [Category* C] {P B X S : C}
    (f : B ⟶ S) (g : X ⟶ S) [HasPullback f g] (b : P ⟶ B) :
    {t : P ⟶ pullback f g // t ≫ pullback.fst f g = b} ≃
      {q : P ⟶ X // q ≫ g = b ≫ f} where
  toFun t := ⟨t.val ≫ pullback.snd f g, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, t.property]⟩
  invFun q := ⟨pullback.lift b q.val q.property.symm, pullback.lift_fst _ _ _⟩
  left_inv t := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans t.property.symm
    · exact pullback.lift_snd _ _ _
  right_inv q := Subtype.ext (pullback.lift_snd _ _ _)

/-- Equality of specified base points changes only the triangle proof. -/
def pointOverEquivOfBaseEq {C : Type*} [Category* C] {P X S : C}
    (f : X ⟶ S) {s t : P ⟶ S} (h : s = t) :
    {q : P ⟶ X // q ≫ f = s} ≃ {q : P ⟶ X // q ≫ f = t} where
  toFun q := ⟨q.val, q.property.trans h⟩
  invFun q := ⟨q.val, q.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

end CategoryTheory
