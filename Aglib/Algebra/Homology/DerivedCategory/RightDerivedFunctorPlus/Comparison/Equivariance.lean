/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.NaturalTransformation

/-! # The original three-factor derived comparison respects coefficient actions

An actual ordinary coefficient square induces equivariance of the same native
three-factor comparison. No action is assumed invertible, and no coefficient
category is required to be linear over a commutative scalar ring.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC uD vD wD
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (U : B ⥤ D) (V : A ⥤ C) (G : C ⥤ D)
  [F.Additive] [U.Additive] [V.Additive] [G.Additive]
  (e : F ⋙ U ≅ V ⋙ G)
  [IsIso (rightDerivedFunctorPlusCompComparison F U)]
  [IsIso (rightDerivedFunctorPlusCompComparison V G)]

/-- The canonical three-factor comparison carries the actual original coefficient action. -/
theorem rightDerivedFunctorPlusThreeFactorIso_equivariant
    (α : U ⟶ U) (β : V ⟶ V)
    (he : whiskerLeft F α ≫ e.hom = e.hom ≫ whiskerRight β G) :
    whiskerLeft F.rightDerivedFunctorPlus (U.rightDerivedFunctorPlusNatTrans α) ≫
        (rightDerivedFunctorPlusThreeFactorIso F U V G e).hom =
      (rightDerivedFunctorPlusThreeFactorIso F U V G e).hom ≫
        whiskerRight (V.rightDerivedFunctorPlusNatTrans β) G.rightDerivedFunctorPlus := by
  let c₁ := rightDerivedFunctorPlusCompIso F U
  let c₂ := rightDerivedFunctorPlusIso (F ⋙ U) e
  let c₃ := rightDerivedFunctorPlusCompIso V G
  let a := (F ⋙ U).rightDerivedFunctorPlusNatTrans (whiskerLeft F α)
  let b := (V ⋙ G).rightDerivedFunctorPlusNatTrans (whiskerRight β G)
  have h₁ : a ≫ c₁.hom = c₁.hom ≫
      whiskerLeft F.rightDerivedFunctorPlus (U.rightDerivedFunctorPlusNatTrans α) :=
    rightDerivedFunctorPlusCompComparison_naturality_right F α
  have h₂ : a ≫ c₂.hom = c₂.hom ≫ b := by
    have h := congrArg
      (fun t : F ⋙ U ⟶ V ⋙ G => (F ⋙ U).rightDerivedFunctorPlusNatTrans t) he
    simpa only [rightDerivedFunctorPlusNatTrans_comp,
      rightDerivedFunctorPlusNatTrans_iso_hom] using h
  have h₃ : b ≫ c₃.hom = c₃.hom ≫
      whiskerRight (V.rightDerivedFunctorPlusNatTrans β) G.rightDerivedFunctorPlus :=
    rightDerivedFunctorPlusCompComparison_naturality_left G β
  change _ ≫ (c₁.inv ≫ c₂.hom ≫ c₃.hom) =
    (c₁.inv ≫ c₂.hom ≫ c₃.hom) ≫ _
  apply (cancel_epi c₁.hom).1
  rw [← Category.assoc, ← h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h₂, Category.assoc, h₃]

end CategoryTheory.Functor
