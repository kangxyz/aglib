/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Group.Pi.Basic

/-! # Product cones certified by their literal section maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AddCommGrpCat

universe u v

/-- A cone of additive groups is a product if its displayed evaluation map is bijective. -/
def fanIsLimitOfBijective {ι : Type u} (G : ι → AddCommGrpCat.{max u v})
    (P : AddCommGrpCat.{max u v}) (f : ∀ i, P ⟶ G i)
    (h : Function.Bijective (fun x : P => fun i => f i x)) :
    IsLimit (Fan.mk P f) := by
  let φ : P →+ ∀ i, G i :=
    { toFun := fun x i => f i x
      map_zero' := by ext i; exact (f i).hom.map_zero
      map_add' := by intros; ext i; exact (f i).hom.map_add _ _ }
  let e : P ≃+ ∀ i, G i := AddEquiv.ofBijective φ h
  let l (s : Fan G) : s.pt ⟶ P := ofHom
    (e.symm.toAddMonoidHom.comp
      { toFun := fun x i => s.proj i x
        map_zero' := by ext i; exact (s.proj i).hom.map_zero
        map_add' := by intros; ext i; exact (s.proj i).hom.map_add _ _ })
  refine Fan.IsLimit.mk _ l ?_ ?_
  · intro s i
    ext x
    exact congrFun (e.apply_symm_apply (fun i => s.proj i x)) i
  · intro s m hm
    ext x
    apply e.injective
    funext i
    have hi := ConcreteCategory.congr_hom (hm i) x
    exact hi.trans (congrFun (e.apply_symm_apply (fun i => s.proj i x)) i).symm

end AddCommGrpCat
