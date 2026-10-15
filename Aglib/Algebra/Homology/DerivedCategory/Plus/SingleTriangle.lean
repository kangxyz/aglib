/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
/-!
# Short exact sequences in the bounded-below derived category

Lift the actual single triangle through the fully faithful bounded-below inclusion.
Its connecting arrow uses the original shift comparison, and forgetting the bound
recovers the original short-exact triangle. No injective hypothesis is required.
-/


/-!
Source: `Quillen/Algebra/Homology/DerivedCategory/PlusSingleTriangle.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 61]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Pretriangulated
namespace CategoryTheory.ShortComplex.ShortExact
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex C} (hS : S.ShortExact)
/-- The original short exact sequence gives a triangle in the bounded-below derived category. -/
def singleTrianglePlus : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g)
    (DerivedCategory.Plus.ι.preimage
      (hS.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)))
/-- Forgetting the bound recovers the actual original short-exact triangle. -/
def singleTrianglePlusιIso :
    DerivedCategory.Plus.ι.mapTriangle.obj (singleTrianglePlus hS) ≅ hS.singleTriangle := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [singleTrianglePlus, Functor.mapTriangle, singleTriangle]
    rfl
  · simp [singleTrianglePlus, Functor.mapTriangle, singleTriangle]
    rfl
  · simp only [Functor.mapTriangle_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      Triangle.mk_obj₃, singleTriangle_obj₁, Triangle.mk_obj₁, Triangle.mk_mor₃,
      Iso.refl_hom, Functor.map_id, Category.comp_id, singleTriangle_obj₃,
      singleTriangle_mor₃, Category.id_comp]
    change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) ≫ _ = _
    rw [Functor.map_preimage]
    rw [Category.assoc]
    change hS.singleδ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id hS.singleδ
/-- The actual bounded-below single triangle is distinguished. -/
theorem singleTrianglePlus_distinguished :
    singleTrianglePlus hS ∈ distTriang (DerivedCategory.Plus C) := by
  apply DerivedCategory.Plus.ι.map_distinguished_iff _ |>.mp
  exact isomorphic_distinguished _ hS.singleTriangle_distinguished _ (singleTrianglePlusιIso hS)
end CategoryTheory.ShortComplex.ShortExact
