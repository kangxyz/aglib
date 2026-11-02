/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Filtered colimits of presheaf sections

Joint surjectivity and eventual equality of sections make the original image
cocone of an additive-group-valued presheaf colimiting. The proof uses the actual
forgetful functor and reflects the colimit property of that same cocone.
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory

universe vI vC uI uC w

private theorem presheaf_comp_apply {C : Type uC} [Category.{vC} C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {A B E : C} (f : A ⟶ B) (g : B ⟶ E)
    (s : P.obj (op E)) :
    P.map f.op (P.map g.op s) = P.map (f ≫ g).op s := by
  exact (ConcreteCategory.congr_hom (P.map_comp g.op f.op) s).symm

/-- Pulling back equal sections along one side of a commuting triangle
preserves their equality along the composite side. -/
theorem presheaf_eq_of_triangle {C : Type uC} [Category.{vC} C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {A B E : C} (f : A ⟶ B) (g : B ⟶ E)
    (a : A ⟶ E) (ha : f ≫ g = a) (s t : P.obj (op E))
    (h : P.map g.op s = P.map g.op t) : P.map a.op s = P.map a.op t := by
  simpa only [presheaf_comp_apply, ha] using congrArg (P.map f.op) h

namespace Limits

/-- A cofiltered presheaf image cocone is colimiting when its original legs are
jointly surjective and equality at one stage is witnessed at a later stage.
The index object and morphism universes fit in the universe of the values. -/
def isColimitPresheafMapConeOfSections
    {I : Type uI} [Category.{vI} I] [IsCofiltered I]
    [UnivLE.{uI, w}] [UnivLE.{vI, w}]
    {C : Type uC} [Category.{vC} C] (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (D : I ⥤ C) (c : Cone D)
    (hsurj : ∀ s : P.obj (op c.pt),
      ∃ (i : I) (v : P.obj (op (D.obj i))), P.map (c.π.app i).op v = s)
    (hinj : ∀ (i : I) (s t : P.obj (op (D.obj i))),
      P.map (c.π.app i).op s = P.map (c.π.app i).op t →
      ∃ (k : I) (q : k ⟶ i), P.map (D.map q).op s = P.map (D.map q).op t) :
    IsColimit (P.mapCocone c.op) := by
  let G := D.op ⋙ P
  have : PreservesFilteredColimitsOfSize.{vI, uI} (CategoryTheory.forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, vI, uI} _
  have : ReflectsColimit G (CategoryTheory.forget AddCommGrpCat.{w}) :=
    reflectsColimit_of_reflectsIsomorphisms G _
  apply isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{w})
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro s
    obtain ⟨i, v, hv⟩ := hsurj s
    exact ⟨op i, v, hv.symm⟩
  · intro i s t h
    obtain ⟨k, q, hq⟩ := hinj i.unop s t h
    exact ⟨op k, q.op, hq⟩

end Limits

end CategoryTheory
