/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor

/-! Degree-zero coefficient transport for the original derived Ext arrows. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

/-- The original shifted Ext morphism retains precomposition and postcomposition by
degree-zero maps. -/
theorem Ext.homPlus_transport_degreeZero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {A B C' D : C} (a : A ⟶ B) (b : C' ⟶ D) (p : ℕ) (x : Ext B C' p) :
    (((Ext.mk₀ a).comp x (zero_add p)).comp (Ext.mk₀ b) (add_zero p)).homPlus =
      (DerivedCategory.Plus.singleFunctor C 0).map a ≫ x.homPlus ≫
        ((DerivedCategory.Plus.singleFunctor C 0).map b)⟦(p : ℤ)⟧' := by
  let S := DerivedCategory.Plus.singleFunctor C 0
  let y : ShiftedHom (S.obj A) (S.obj C') (p : ℤ) :=
    (ShiftedHom.mk₀ 0 rfl (S.map a)).comp x.homPlus (add_zero _)
  have h₁ := ShiftedHom.comp_mk₀ y 0 rfl (S.map b)
  have h₂ := ShiftedHom.mk₀_comp 0 rfl (S.map a) x.homPlus
  simp only [Ext.homPlus_comp, Ext.homPlus_mk₀]
  exact h₁.trans ((congrArg (fun z => z ≫ (S.map b)⟦(p : ℤ)⟧') h₂).trans
    (Category.assoc _ _ _))

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- Transport an original exact-single comparison along a specified coefficient isomorphism. -/
def rightDerivedFunctorPlusSingleIsoOfIso (q : ℤ) {M : C} {N : D}
    (i : F.obj M ≅ N) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C q).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D q).obj N :=
  (F.rightDerivedFunctorPlusSingleIso q).app M ≪≫
    (DerivedCategory.Plus.singleFunctor D q).mapIso i

variable [HasExt C] [HasExt D] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]

/-- Actual precomposition and postcomposition before and after exact forgetting. -/
theorem mapExactFunctor_prePost_homPlus {A B : C} {A' B' : D}
    (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B') (q : ℕ) (x : Ext A B q) :
    let S := DerivedCategory.Plus.singleFunctor D 0
    let e := F.rightDerivedFunctorPlusSingleIso 0
    (((Ext.mk₀ a).comp (x.mapExactFunctor F) (zero_add q)).comp
        (Ext.mk₀ b) (add_zero q)).homPlus =
      S.map a ≫ e.inv.app A ≫ x.homPlus.map F.rightDerivedFunctorPlus ≫
        (e.hom.app B ≫ S.map b)⟦(q : ℤ)⟧' := by
  intro S e
  rw [Ext.homPlus_transport_degreeZero, ← F.rightDerivedFunctorPlusSingleIso_map_homPlus x]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Exact inverse image on Ext, with its two original degree-zero transports,
is the same shifted morphism in the original bounded-below derived category. -/
theorem mapExactFunctor_transport_homPlus {A B : C} {A' B' : D}
    (a : F.obj A ≅ A') (b : F.obj B ≅ B') (p : ℕ) (x : Ext A B p) :
    (((Ext.mk₀ a.inv).comp (x.mapExactFunctor F) (zero_add p)).comp
      (Ext.mk₀ b.hom) (add_zero p)).homPlus =
      (F.rightDerivedFunctorPlusSingleIsoOfIso 0 a).inv ≫
        x.homPlus.map F.rightDerivedFunctorPlus ≫
          (F.rightDerivedFunctorPlusSingleIsoOfIso 0 b).hom⟦(p : ℤ)⟧' := by
  rw [Ext.homPlus_transport_degreeZero, ← F.rightDerivedFunctorPlusSingleIso_map_homPlus x]
  simp only [rightDerivedFunctorPlusSingleIsoOfIso, Iso.app_inv, Iso.app_hom, Iso.trans_inv,
    Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end CategoryTheory.Functor
