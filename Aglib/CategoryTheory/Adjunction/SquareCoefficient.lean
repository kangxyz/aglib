/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Coefficient arrows across an original adjunction square

The complete transposition retains the native transported composite adjunction
and its original uniqueness isomorphism. It introduces no alternate mate.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
  {i : A ⥤ C} {I : C ⥤ A} {j : B ⥤ D} {J : D ⥤ B}
  (a : L ⊣ R) (b : L' ⊣ R') (c : i ⊣ I) (d : j ⊣ J)
  (e : J ⋙ R ≅ R' ⋙ I)

/-- A square of the actual adjoint coefficient arrows transposes through the
original left-adjoint uniqueness comparison. -/
theorem coefficient_square_of_homEquiv
    {M : A} {N : B} {M' : C} {N' : D}
    (α : L.obj M ⟶ N) (β : j.obj N ⟶ N')
    (γ : i.obj M ⟶ M') (δ : L'.obj M' ⟶ N')
    (h : a.homEquiv _ _ α ≫ R.map (d.homEquiv _ _ β) ≫ e.hom.app N' =
      c.homEquiv _ _ γ ≫ I.map (b.homEquiv _ _ δ)) :
    j.map α ≫ β =
      (((a.comp d).ofNatIsoRight e).leftAdjointUniq (c.comp b)).hom.app M ≫
        L'.map γ ≫ δ := by
  let t := (a.comp d).ofNatIsoRight e
  have ht (k : L'.obj (i.obj M) ⟶ N') :
      t.homEquiv _ _ ((t.leftAdjointUniq (c.comp b)).hom.app M ≫ k) =
        (c.comp b).homEquiv _ _ k := by
    rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, ← Category.assoc,
      unit_leftAdjointUniq_hom_app]
  apply (t.homEquiv _ _).injective
  rw [ht]
  simp only [t, homEquiv_ofNatIsoRight_apply, comp_homEquiv, Equiv.trans_apply]
  rw [d.homEquiv_naturality_left, b.homEquiv_naturality_left,
    a.homEquiv_naturality_right, c.homEquiv_naturality_right]
  simpa only [Category.assoc] using h

end CategoryTheory.Adjunction
