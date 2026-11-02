/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Point.SectionValues

/-! # Original whole chart values before section projection

The same coefficient transformations are compared while their functors are
variables. Their actual equality transports the primitive scalar law before
the original chart map and section homomorphism are projected.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v

namespace CategoryTheory.OriginalSectionValues

/-- A proved whole coefficient value equality transports the actual section law. -/
theorem chartSectionHom_of_whole_values
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    (P : C ⥤ D) (K : C ⥤ E) (R : E ⥤ H) (I : D ⥤ H)
    (Γ : H ⥤ AddCommGrpCat.{v}) (α α₀ : P ⋙ I ⟶ K ⋙ R) (hα : α = α₀)
    (F : C) {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {Z : AddCommGrpCat.{v}} (evaluation : Γ.obj (I.obj (P.obj F)) ≅ Z)
    (source : A →+ Z) (comparison : A ≃+ B)
    (higher : B →+ Γ.obj (R.obj (K.obj F)))
    (h : ∀ x, Γ.map (α₀.app F) (evaluation.inv (source x)) = higher (comparison x)) :
    (chartSectionMapOfHom Γ evaluation (α.app F)).hom.comp source =
      higher.comp comparison.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  have hcomponent : α.app F = α₀.app F := NatTrans.congr_app hα F
  have hx := (congrArg (fun b => Γ.map b (evaluation.inv (source x))) hcomponent).trans
    (h x)
  simpa only [Functor.comp_obj, chartSectionMapOfHom, AddMonoidHom.comp_apply,
    AddCommGrpCat.Hom.hom, ConcreteCategory.comp_apply, AddEquiv.coe_toAddMonoidHom] using hx

end CategoryTheory.OriginalSectionValues
