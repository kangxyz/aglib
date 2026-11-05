/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Coproducts.CoefficientComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.HomologyNaturality
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.SingleNaturality

/-! # The original higher-image coefficient comparison retains scalar equivariance -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

private theorem inverse_intertwines {T : Type*} [Category* T]
    {X Y : T} (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : a ≫ e.hom = e.hom ≫ b) : b ≫ e.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] [HasDerivedCategory.{w₃} A']
  [EnoughInjectives A']
  {B' : Type u₄} [Category.{v₄} B'] [Abelian B'] [HasDerivedCategory.{w₄} B']
  (F : A ⥤ B) (F' : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
  [F.Additive] [F'.Additive] [U.Additive] [V.Additive]
  [U.PreservesHomology] [V.PreservesHomology]
  (e : F.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ≅
    U.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus)

/-- Equivariance of the actual derived comparison passes through its original five factors. -/
theorem rightDerivedExactCoefficientIso_equivariant
    (α : U ⟶ U) (β : V ⟶ V)
    (he : whiskerLeft F.rightDerivedFunctorPlus (V.rightDerivedFunctorPlusNatTrans β) ≫
      e.hom = e.hom ≫ whiskerRight (U.rightDerivedFunctorPlusNatTrans α)
        F'.rightDerivedFunctorPlus) (n : ℕ) :
    whiskerLeft (F.rightDerived n) β ≫ (rightDerivedExactCoefficientIso F F' U V e n).hom =
      (rightDerivedExactCoefficientIso F F' U V e n).hom ≫
        whiskerRight α (F'.rightDerived n) := by
  ext M
  let K := (DerivedCategory.Plus.singleFunctor A 0).obj M
  let H := DerivedCategory.Plus.homologyFunctor B' (n : ℤ)
  let L₁ := V.map ((F.rightDerivedSingleHomologyIso n).hom.app M)
  let L₂ := (V.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
    (F.rightDerivedFunctorPlus.obj K)
  let L₃ := H.map (e.hom.app K)
  let L₄ := H.map (F'.rightDerivedFunctorPlus.map
    ((U.rightDerivedFunctorPlusSingleIso 0).hom.app M))
  let L₅ := (F'.rightDerivedSingleHomologyIso n).inv.app (U.obj M)
  have h₁ := (β.naturality ((F.rightDerivedSingleHomologyIso n).hom.app M)).symm
  have h₂ := inverse_intertwines
    ((V.rightDerivedFunctorPlusHomologyIso (n : ℤ)).app (F.rightDerivedFunctorPlus.obj K))
    (H.map ((V.rightDerivedFunctorPlusNatTrans β).app (F.rightDerivedFunctorPlus.obj K)))
    (β.app ((DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj K)))
    (NatTrans.congr_app (rightDerivedFunctorPlusHomologyIso_naturality β (n : ℤ))
      (F.rightDerivedFunctorPlus.obj K))
  have h₃ := congrArg H.map (NatTrans.congr_app he K)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp] at h₃
  have h₄ := congrArg (fun k => H.map (F'.rightDerivedFunctorPlus.map k))
    (NatTrans.congr_app (rightDerivedFunctorPlusSingleIso_naturality α) M)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp] at h₄
  have h₅ := (F'.rightDerivedSingleHomologyIso n).inv.naturality (α.app M)
  simp only [Functor.comp_obj] at h₁
  simp only [Iso.app_inv] at h₂
  simp only [Functor.comp_map] at h₅
  dsimp only [K] at h₂ h₃
  change _ ≫ (L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅) = (L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅) ≫ _
  dsimp only [L₁, L₂, L₃, L₄, L₅, K]
  simp only [whiskerLeft_app, whiskerRight_app, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]

end CategoryTheory.Functor
