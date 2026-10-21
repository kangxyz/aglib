/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Map squares for composite functor comparisons

The original natural comparison and objectwise coordinate isomorphisms define
one shared square predicate. Compatibility follows from the two original local
squares before any concrete categories, functors, or coefficients are supplied.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  {R : C ⥤ D} (T : C ⥤ E) (P : D ⥤ E) (α : T ≅ R ⋙ P)
  {X Y : C} (g : X ⟶ Y) {N N' : D}
  (eX : R.obj X ≅ N) (eY : R.obj Y ≅ N')
  {Z Z' : E} (βX : P.obj N ≅ Z) (βY : P.obj N' ≅ Z') (h : Z ⟶ Z')

/-- The original map square through a natural comparison and two objectwise
coordinate comparisons, retaining the literal original composites. -/
def mapComparisonSquare : Prop :=
  T.map g ≫ (α.app Y ≪≫ P.mapIso eY ≪≫ βY).hom =
    (α.app X ≪≫ P.mapIso eX ≪≫ βX).hom ≫ h

/-- Compatibility of the two local maps implies compatibility of the original
composite comparisons. -/
theorem mapComparisonSquare_of_local_squares (k : N ⟶ N')
    (hg : R.map g ≫ eY.hom = eX.hom ≫ k)
    (hk : P.map k ≫ βY.hom = βX.hom ≫ h) :
    mapComparisonSquare T P α g eX eY βX βY h := by
  have hα : T.map g ≫ (α.app Y).hom =
      (α.app X).hom ≫ P.map (R.map g) := α.hom.naturality g
  have hP := congrArg P.map hg
  simp only [Functor.map_comp] at hP
  unfold mapComparisonSquare
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc (T.map g) (α.app Y).hom, hα]
  simp only [Category.assoc]
  rw [← Category.assoc (P.map (R.map g)) (P.map eY.hom), hP]
  simp only [Category.assoc]
  rw [hk]

end CategoryTheory.Functor
