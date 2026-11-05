/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantActionNatTrans

/-! # Lift original scalar-compatible underlying isomorphisms

The source category has no scalar-linearity hypothesis. The inverse scalar
law follows from the given original forward law and the original inverse.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf
universe u v r w h
variable {C : Type u} [Category.{v} C] (R : Type r) [Ring R]
  (J : GrothendieckTopology C)
  {D : Type w} [Category.{h} D]
  (P Q : D ⥤ CategoryTheory.Sheaf J (ModuleCat.{max u v} R))
  (e : P ⋙ underlying R J ≅ Q ⋙ underlying R J)
  (he : ∀ (F : D) (a : R),
    (underlyingScalar J R a).app (P.obj F) ≫ e.hom.app F =
      e.hom.app F ≫ (underlyingScalar J R a).app (Q.obj F))

include he in
/-- The original inverse intertwines the same two scalar actions. -/
theorem underlyingAction_iso_inv (F : D) (a : R) :
    (underlyingScalar J R a).app (Q.obj F) ≫ e.inv.app F =
      e.inv.app F ≫ (underlyingScalar J R a).app (P.obj F) := by
  apply (cancel_mono (e.hom.app F)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [he F a]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.id_comp]

/-- Lift the actual underlying isomorphism without changing either original map. -/
def natIsoOfUnderlyingAction : P ≅ Q where
  hom := natTransOfUnderlyingAction R J P Q e.hom he
  inv := natTransOfUnderlyingAction R J Q P e.inv
    (underlyingAction_iso_inv R J P Q e he)
  hom_inv_id := by
    apply NatTrans.ext
    funext F
    apply (underlying R J).map_injective
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp,
      underlying_map_natTransOfUnderlyingAction]
    exact e.hom_inv_id_app F
  inv_hom_id := by
    apply NatTrans.ext
    funext F
    apply (underlying R J).map_injective
    simp only [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp,
      underlying_map_natTransOfUnderlyingAction]
    exact e.inv_hom_id_app F

/-- The lifted forward component retains the exact given underlying map. -/
@[simp]
theorem underlying_map_natIsoOfUnderlyingAction_hom (F : D) :
    (underlying R J).map ((natIsoOfUnderlyingAction R J P Q e he).hom.app F) =
      e.hom.app F := rfl

/-- The lifted inverse component retains the exact given underlying map. -/
@[simp]
theorem underlying_map_natIsoOfUnderlyingAction_inv (F : D) :
    (underlying R J).map ((natIsoOfUnderlyingAction R J P Q e he).inv.app F) =
      e.inv.app F := rfl

end ModuleCat.Sheaf
