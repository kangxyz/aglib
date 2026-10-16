/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans
public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Shifts of original bounded-below complex comparisons

The original componentwise natural transformation and the original
composition comparison commute with native integer shifts. Their chain
components are unchanged; this supplies shift compatibility of installed
right-derived composition units and geometric base-change descents.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v u' v' u'' v''

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- The original componentwise map on bounded-below complexes commutes
with integer shifts, without changing its chain components. -/
instance NatTrans.mapCochainComplexPlus_commShift (α : F ⟶ G) :
    (NatTrans.mapCochainComplexPlus α).CommShift ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι B) (h := ?_)
  have h : Functor.whiskerRight (NatTrans.mapCochainComplexPlus α)
      (CochainComplex.Plus.ι B) =
        F.mapCochainComplexPlusCompι.hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A)
            (NatTrans.mapHomologicalComplex α (.up ℤ)) ≫
          G.mapCochainComplexPlusCompι.inv := by
    ext K i
    change α.app (K.obj.X i) = 𝟙 _ ≫ α.app (K.obj.X i) ≫ 𝟙 _
    simp
  rw [h]
  infer_instance

variable {C : Type u''} [Category.{v''} C] [Preadditive C]
    (F : A ⥤ B) [F.Additive] (H : B ⥤ C) [H.Additive]

/-- The original identity-component composition comparison retains the
native shift structures of all three termwise functors. -/
instance Functor.mapCochainComplexPlusCompIso_commShift :
    (Functor.mapCochainComplexPlusCompIso F H).hom.CommShift ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι C) (h := ?_)
  let e := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H)) (.up ℤ)
  have h : Functor.whiskerRight (Functor.mapCochainComplexPlusCompIso F H).hom
      (CochainComplex.Plus.ι C) =
        (F ⋙ H).mapCochainComplexPlusCompι.hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A) e.inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight F.mapCochainComplexPlusCompι.inv
            (H.mapHomologicalComplex (.up ℤ)) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft F.mapCochainComplexPlus H.mapCochainComplexPlusCompι.inv ≫
          (Functor.associator _ _ _).inv := by
    ext K i
    simp [Functor.mapCochainComplexPlusCompIso, e]
  rw [h]
  infer_instance

end CategoryTheory
