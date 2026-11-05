/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.IsIsoOn

/-! # Pointwise-to-whole invertibility of the original restricted transformation

The full-subcategory object projection, whiskered component equality and
pointwise IsIso family are processed with both original functors variable.
No concrete geometric component is unfolded at the consumer boundary.
-/

@[expose] public noncomputable section
namespace CategoryTheory

universe u v w t

/-- Invertibility on an object property supplies invertibility of the actual
whiskered transformation, without returning any component isomorphism. -/
theorem NatTrans.isIso_whiskerLeft_of_isIsoOn
    {C : Type u} [Category.{v} C] {D : Type w} [Category.{t} D]
    {F G : C ⥤ D} (α : F ⟶ G) (P : ObjectProperty C)
    (hα : NatTrans.IsIsoOn P α) : IsIso (Functor.whiskerLeft P.ι α) := by
  let : ∀ K : P.FullSubcategory, IsIso ((Functor.whiskerLeft P.ι α).app K) :=
    fun K => hα K.obj K.property
  exact NatIso.isIso_of_isIso_app (Functor.whiskerLeft P.ι α)

end CategoryTheory
