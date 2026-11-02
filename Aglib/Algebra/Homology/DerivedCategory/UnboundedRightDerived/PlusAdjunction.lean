/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.UnitExpansion
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The original adjunction across bounded-below inclusion

The fixed exact-left and actual right-derived comparisons preserve the original
adjunction unit. Thus their vertical square has the specified right comparison
as its actual mate, not merely as an isomorphism of the same objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe s u v w u' v' w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [IsGrothendieckAbelian.{s} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ R)

/-- On each original bounded-below complex the two fixed comparisons preserve
its actual adjunction unit. -/
theorem unboundedRightDerivedAdjunction_plus_unit_Q (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map
        (adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K)) ≫
      R.unboundedRightDerivedFunctorPlusIso.hom.app
        (L.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      R.unboundedRightDerivedFunctor.map
        (L.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K)) =
      adj.unboundedRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj K.obj) := by
  rw [adj.rightDerivedFunctorPlus_unit_eq K]
  simp only [Functor.map_comp, Category.assoc]
  have hn := R.unboundedRightDerivedFunctorPlusIso.hom.naturality
    (L.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (R.unboundedRightDerivedFunctorPlusIso_unit_app
    (L.mapCochainComplexPlus.obj K))]
  rw [← R.unboundedRightDerivedFunctor.map_comp]
  have hL : DerivedCategory.Plus.ι.map (L.rightDerivedFunctorPlusUnit.app K) ≫
      L.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) =
      L.mapDerivedCategoryFactors.inv.app K.obj := by
    simpa using L.rightDerivedFunctorPlusCompιIso_unit K
  rw [hL]
  apply (cancel_mono (R.unboundedRightDerivedFunctor.map
    (L.mapDerivedCategoryFactors.hom.app K.obj))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  let a := DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Q.map (adj.mapCochainComplexPlus.unit.app K))
  let b := R.unboundedRightDerivedFunctorUnit.app (L.mapCochainComplexPlus.obj K).obj
  have hi := R.unboundedRightDerivedFunctor.map_id
    (DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj K.obj))
  exact ((congrArg (fun z => a ≫ b ≫ z) hi).trans
    (congrArg (fun z => a ≫ z) (Category.comp_id b))).trans
      (adj.unboundedRightDerivedAdjunction_unit_app K.obj).symm

/-- The fixed bounded-below comparisons preserve the original adjunction unit
on every native bounded-below derived object. -/
theorem unboundedRightDerivedAdjunction_plus_unit (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map (adj.rightDerivedFunctorPlus.unit.app X) ≫
      R.unboundedRightDerivedFunctorPlusIso.hom.app (L.rightDerivedFunctorPlus.obj X) ≫
      R.unboundedRightDerivedFunctor.map (L.rightDerivedFunctorPlusCompιIso.hom.app X) =
      adj.unboundedRightDerivedAdjunction.unit.app X.obj := by
  let a := adj.rightDerivedFunctorPlus
  let b := adj.unboundedRightDerivedAdjunction
  let l := L.rightDerivedFunctorPlusCompιIso
  let r := R.unboundedRightDerivedFunctorPlusIso
  have h : (leftUnitor (DerivedCategory.Plus.ι (C := C))).inv ≫
      whiskerRight a.unit DerivedCategory.Plus.ι ≫
      (associator _ _ _).hom ≫ whiskerLeft L.rightDerivedFunctorPlus r.hom ≫
      (associator _ _ _).inv ≫ whiskerRight l.hom R.unboundedRightDerivedFunctor ≫
      (associator _ _ _).hom =
      (rightUnitor (DerivedCategory.Plus.ι (C := C))).inv ≫
        whiskerLeft DerivedCategory.Plus.ι b.unit := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
    intro K
    simpa only [DerivedCategory.Plus.Q, ObjectProperty.lift,
      a, b, l, r, Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, NatTrans.comp_app,
      leftUnitor_inv_app, rightUnitor_inv_app,
      whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
        adj.unboundedRightDerivedAdjunction_plus_unit_Q K
  simpa only [a, b, l, r, Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, NatTrans.comp_app,
      leftUnitor_inv_app, rightUnitor_inv_app,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app h X

end CategoryTheory.Adjunction
