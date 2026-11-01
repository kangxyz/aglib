/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.NatIso

/-!
# Original natural isomorphisms lifted to a native full subcategory

The components retain the exact original underlying morphisms. This abstract
construction transports their identity and composition laws before any scheme
or derived-category specialization.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D]
  (P : ObjectProperty D) (F G H : C ⥤ D)
  (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) (hH : ∀ X, P (H.obj X))

/-- Lift a specified natural isomorphism without changing its underlying maps. -/
def liftFunctorIso (e : F ≅ G) : P.lift F hF ≅ P.lift G hG :=
  NatIso.ofComponents (fun X => P.isoMk (e.app X)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f)

/-- Every lifted component is the original underlying component. -/
theorem liftFunctorIso_hom_app (e : F ≅ G) (X : C) :
    ((P.liftFunctorIso F G hF hG e).hom.app X).hom = e.hom.app X := rfl

/-- Lifting preserves the identity natural isomorphism. -/
@[simp]
theorem liftFunctorIso_refl :
    P.liftFunctorIso F F hF hF (Iso.refl F) = Iso.refl (P.lift F hF) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  rfl

/-- Lifting retains the original composition of natural isomorphisms. -/
theorem liftFunctorIso_trans (e : F ≅ G) (e' : G ≅ H) :
    P.liftFunctorIso F G hF hG e ≪≫ P.liftFunctorIso G H hG hH e' =
      P.liftFunctorIso F H hF hH (e ≪≫ e') := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  rfl

end CategoryTheory.ObjectProperty
