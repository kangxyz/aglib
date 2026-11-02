/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Original fibres on pointed site slices

The native category of pointed slice neighborhoods is equivalent to the
slice of the original category of elements. Its forgetful functor is initial,
so the original colimit comparisons preserve every original germ map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

universe u v w uA vA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : Point.{w} J) {U : C} (x : Φ.fiber.obj U)
  {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{w, w} A]

/-- The actual pointed-slice neighborhood forgetful functor. -/
def overElementsForget : (Φ.over x).fiber.Elements ⥤ Φ.fiber.Elements :=
  (FunctorToTypes.fromOverSubfunctor Φ.fiber x).ι.mapElements ⋙
    Functor.Elements.precomp (Over.forget U) Φ.fiber

instance overElementsForget_initial : (Φ.overElementsForget x).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    let z := IsCofiltered.min (Φ.fiber.elementsMk U x) d
    let q := IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) d
    let V : Over U := Over.mk q.hom
    let y : (Φ.over x).fiber.obj V := ⟨z.val,
      (FunctorToTypes.mem_fromOverSubfunctor_iff Φ.fiber x _).mpr q.map_val⟩
    exact ⟨(Φ.over x).fiber.elementsMk V y,
      ⟨IsCofiltered.minToRight (Φ.fiber.elementsMk U x) d⟩⟩
  · intro d c s t
    let z := IsCofiltered.eq s t
    let q := IsCofiltered.eqHom s t
    let V : Over U := Over.mk (q.hom ≫ c.obj.hom)
    let y : (Φ.over x).fiber.obj V := ⟨z.val, by
      apply (FunctorToTypes.mem_fromOverSubfunctor_iff Φ.fiber x _).mpr
      change Φ.fiber.map (q.hom ≫ c.obj.hom) z.val = x
      exact (ConcreteCategory.congr_hom
        (Φ.fiber.map_comp q.hom c.obj.hom) z.val).trans
          ((congrArg (Φ.fiber.map c.obj.hom) q.map_val).trans
            ((FunctorToTypes.mem_fromOverSubfunctor_iff Φ.fiber x _).mp c.val.2))⟩
    refine ⟨(Φ.over x).fiber.elementsMk V y,
      Functor.Elements.homMk (Over.homMk q.hom) ?_, ?_⟩
    · apply Subtype.ext
      exact q.map_val
    · exact IsCofiltered.eq_condition s t

/-- The original pointed slice fibre comparison. -/
def overPresheafFiberIso (P : Cᵒᵖ ⥤ A) :
    (Φ.over x).presheafFiber.obj ((Over.forget U).op ⋙ P) ≅ Φ.presheafFiber.obj P :=
  Functor.Final.colimitIso (Φ.overElementsForget x).op
    ((Functor.Elements.π Φ.fiber).op ⋙ P)

/-- The comparison preserves the original germ at every pointed slice object. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_overPresheafFiberIso_hom
    (P : Cᵒᵖ ⥤ A) (V : Over U) (y : (Φ.over x).fiber.obj V) :
    (Φ.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
        (Φ.overPresheafFiberIso x P).hom =
      Φ.toPresheafFiber V.left y.1 P :=
  Functor.Final.ι_colimitIso_hom (Φ.overElementsForget x).op
    ((Functor.Elements.π Φ.fiber).op ⋙ P) (op ((Φ.over x).fiber.elementsMk V y))

end CategoryTheory.GrothendieckTopology.Point
