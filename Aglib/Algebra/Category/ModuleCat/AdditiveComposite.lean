/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Evaluation of the original mixed linear and additive comparison

The original isomorphism homs are retained while forgetting the middle linear
comparison to its additive equivalence. Independent module and group value
universes are preserved. This whole evaluation law avoids unfolding concrete
module/sheaf constructions merely to normalize the composite's forward map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe r v w z c c' d d'

namespace CategoryTheory.Iso

variable {R : Type r} [Ring R] {M N : ModuleCat.{v} R}
  {H : Type w} [AddCommGroup H] [Module R H] {K L : AddCommGrpCat.{z}}

/-- Compose the actual module isomorphism, linear comparison, additive comparison
and final additive-category isomorphism, retaining each original factor. -/
def moduleAdditiveComposite (i : M ≅ N) (l : N ≃ₗ[R] H)
    (a : H ≃+ K) (b : K ≅ L) : M ≃+ L := by
  let e := i.toLinearEquiv.toAddEquiv.trans
    (l.toAddEquiv.trans (a.trans b.addCommGroupIsoToAddEquiv))
  exact
    { toFun := fun x => b.hom (a (l (i.hom x)))
      invFun := fun y => i.inv (l.symm (a.symm (b.inv y)))
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add }

/-- The complete mixed comparison has exactly the original forward maps. -/
theorem moduleAdditiveComposite_apply (i : M ≅ N) (l : N ≃ₗ[R] H)
    (a : H ≃+ K) (b : K ≅ L) (x : M) :
    moduleAdditiveComposite i l a b x =
      b.hom (a (l (i.hom x))) := rfl

/-- Evaluation after mapping both original categorical isomorphisms. The
functorial homs are normalized before any geometric category is instantiated. -/
theorem moduleAdditiveComposite_mapIso_apply
    {C : Type c} [Category.{c'} C] {D : Type d} [Category.{d'} D]
    (F : C ⥤ ModuleCat.{v} R) (G : D ⥤ AddCommGrpCat.{z})
    {X Y : C} {P Q : D} (i : X ≅ Y)
    (l : F.obj Y ≃ₗ[R] H) (a : H ≃+ G.obj P) (b : P ≅ Q)
    (x : F.obj X) :
    moduleAdditiveComposite (F.mapIso i) l a (G.mapIso b) x =
      G.map b.hom (a (l (F.map i.hom x))) := rfl

end CategoryTheory.Iso
