/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.TripleCompositionTransport

/-! # The same original composition square in structural contraction form -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {J S : A ⥤ C} {J₁ S₁ : A ⥤ B} {J₂ S₂ : B ⥤ C}

/-- Literal structural contraction form of an original outer-adjoint composition square. -/
def OpenCompositionToTargetEquation (b : J ⟶ S) (b₁ : J₁ ⟶ S₁) (b₂ : J₂ ⟶ S₂)
    (c : J₁ ⋙ J₂ ≅ J) (e : S₁ ⋙ S₂ ≅ S) : Prop :=
  ∀ K, c.hom.app K ≫ b.app K =
    J₂.map (b₁.app K) ≫ b₂.app (S₁.obj K) ≫ e.hom.app K

/-- Reorienting the proved original square changes none of its maps. -/
theorem openCompositionToTarget_of_square
    (b : J ⟶ S) (b₁ : J₁ ⟶ S₁) (b₂ : J₂ ⟶ S₂)
    (c : J ≅ J₁ ⋙ J₂) (e : S ≅ S₁ ⋙ S₂)
    (h : c.hom ≫ Functor.whiskerRight b₁ J₂ ≫ Functor.whiskerLeft S₁ b₂ = b ≫ e.hom) :
    OpenCompositionToTargetEquation b b₁ b₂ c.symm e.symm := by
  intro K
  have hK := congrArg (fun z => c.inv.app K ≫ z.app K ≫ e.inv.app K) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at hK
  exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans hK.symm)
end CategoryTheory
