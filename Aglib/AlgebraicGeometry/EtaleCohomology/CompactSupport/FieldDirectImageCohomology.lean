/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSectionsUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DerivedUnit
public import Aglib.CategoryTheory.Adjunction.ShiftedHom
public import Mathlib.CategoryTheory.Linear.Basic

/-! Original module-unit cohomology as sections of the native direct image. -/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open CategoryTheory CategoryTheory.Abelian

universe u wS wX wE

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section FieldEvaluation

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]

omit [IsSepClosed Ω] in
private theorem fieldUnitSections_eq_additive (M : ModuleSheaf (Spec (.of Ω)) Λ)
    (s : moduleUnit (Spec (.of Ω)) Λ ⟶ M) :
    moduleFieldUnitSectionsEquiv Ω Λ M s = moduleUnitSectionsAddEquiv (Spec (.of Ω)) Λ M s := by
  rw [moduleUnitSectionsAddEquiv_apply]
  unfold moduleFieldUnitSectionsEquiv
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  rfl

variable [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of Ω)) Λ)]

/-- The actual homogeneous unit evaluation is additive. -/
@[no_expose]
def moduleFieldDerivedUnitHomologyAddEquiv
    (q : ℤ) (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ)) :
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q).obj
        (moduleUnit (Spec (.of Ω)) Λ) ⟶ K) ≃+
      (moduleGlobalSections (Spec (.of Ω)) Λ).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q).obj K) where
  toEquiv := moduleFieldDerivedUnitHomologyEquiv Ω Λ q K
  map_add' := by
    intro a b
    change moduleFieldDerivedUnitHomologyMap Ω Λ q K (a + b) =
      moduleFieldDerivedUnitHomologyMap Ω Λ q K a + moduleFieldDerivedUnitHomologyMap Ω Λ q K b
    unfold moduleFieldDerivedUnitHomologyMap
    simp only [fieldUnitSections_eq_additive, Functor.map_add, Preadditive.comp_add, map_add]

/-- The additive refinement uses the same inverse homogeneous evaluation. -/
theorem moduleFieldDerivedUnitHomologyAddEquiv_symm_apply
    (q : ℤ) (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
    (x : (moduleGlobalSections (Spec (.of Ω)) Λ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q).obj K)) :
    (moduleFieldDerivedUnitHomologyAddEquiv Ω Λ q K).symm x =
      (moduleFieldDerivedUnitHomologyEquiv Ω Λ q K).symm x := by
  unfold moduleFieldDerivedUnitHomologyAddEquiv
  rfl

end FieldEvaluation

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of Ω)) (n : ℕ)
  [HasDerivedCategory.{wS} (ModuleSheaf (Spec (.of Ω)) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wE} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- Cohomology from the original unit on the total space gives sections of the
same native higher direct image over a separably closed field. -/
@[no_expose]
def moduleFieldDirectImageHomologyAddEquiv
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Spec (.of Ω)
    Ext.{wE} (moduleUnit X Λ) M q ≃+
      (moduleGlobalSections S Λ).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ)).obj
          ((moduleDerivedDirectImage Λ f).obj
            ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj M))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let S := Spec (.of Ω)
  let C := ModuleSheaf X Λ
  let D := ModuleSheaf S Λ
  let B := DerivedCategory.Plus D
  let U := moduleUnit X Λ
  let I := moduleUnit S Λ
  let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
  let I₀ := (DerivedCategory.Plus.singleFunctor D 0).obj I
  let R := moduleDerivedDirectImage Λ f
  let K := R.obj M₀
  let e₁ := Ext.homPlusAddEquiv (X := U) (Y := M) q
  let F := moduleInverseImage f Λ
  let u := ((F.rightDerivedFunctorPlusSingleIso 0).app I) ≪≫
    (DerivedCategory.Plus.singleFunctor C 0).mapIso (moduleUnitInverseImageIso f n)
  let e₂ := (Linear.homCongr ℤ u.symm (Iso.refl (M₀⟦(q : ℤ)⟧))).toAddEquiv
  let e₃ := (moduleDerivedAdjunction Λ f).homAddEquiv I₀ (M₀⟦(q : ℤ)⟧)
  let e₄ := (Linear.homCongr ℤ (Iso.refl I₀) ((R.commShiftIso (q : ℤ)).app M₀)).toAddEquiv
  let shift := shiftEquiv' B (-(q : ℤ)) (q : ℤ) (by omega)
  let : shift.functor.Additive := Functor.additive_of_preserves_binary_products _
  let e₅ := (shift.toAdjunction.homAddEquiv I₀ K).symm
  let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).app I
  let e₆ := (Linear.homCongr ℤ t (Iso.refl K)).toAddEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans
    (moduleFieldDerivedUnitHomologyAddEquiv Ω Λ (q : ℤ) K))))))


/-- The original field homogeneous evaluation recovers the shifted adjunct of
the same original Ext class, with its original single and degree transports. -/
theorem moduleFieldDirectImageHomologyAddEquiv_hom_value
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (x : Ext (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) :
    let Λ := ULift.{u + 1} (ZMod n)
    let S := Spec (.of Ω)
    let C := ModuleSheaf X Λ
    let D := ModuleSheaf S Λ
    let B := DerivedCategory.Plus D
    let I := moduleUnit S Λ
    let I₀ := (DerivedCategory.Plus.singleFunctor D 0).obj I
    let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
    let K := (moduleDerivedDirectImage Λ f).obj M₀
    let F := moduleInverseImage f Λ
    let u := ((F.rightDerivedFunctorPlusSingleIso 0).app I) ≪≫
      (DerivedCategory.Plus.singleFunctor C 0).mapIso (moduleUnitInverseImageIso f n)
    let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
      (by omega)).app I
    (moduleFieldDerivedUnitHomologyAddEquiv Ω Λ (q : ℤ) K).symm
        (moduleFieldDirectImageHomologyAddEquiv Ω f n M q x) =
      t.inv ≫ ((shiftEquiv' B (-(q : ℤ)) (q : ℤ) (by omega)).toAdjunction.homEquiv I₀ K).symm
        ((moduleDerivedAdjunction Λ f).shiftedHomEquiv (q : ℤ) I₀ M₀ (u.hom ≫ x.homPlus)) := by
  dsimp only
  let Λ := ULift.{u + 1} (ZMod n)
  let S := Spec (.of Ω)
  let C := ModuleSheaf X Λ
  let D := ModuleSheaf S Λ
  let B := DerivedCategory.Plus D
  let U := moduleUnit X Λ
  let I := moduleUnit S Λ
  let I₀ := (DerivedCategory.Plus.singleFunctor D 0).obj I
  let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
  let R := moduleDerivedDirectImage Λ f
  let K := R.obj M₀
  let F := moduleInverseImage f Λ
  let u := ((F.rightDerivedFunctorPlusSingleIso 0).app I) ≪≫
    (DerivedCategory.Plus.singleFunctor C 0).mapIso (moduleUnitInverseImageIso f n)
  let t := ((DerivedCategory.Plus.singleFunctors D).shiftIso (-(q : ℤ)) (q : ℤ) 0
    (by omega)).app I
  let shift := shiftEquiv' B (-(q : ℤ)) (q : ℤ) (by omega)
  let : shift.functor.Additive := Functor.additive_of_preserves_binary_products _
  let s := shift.toAdjunction
  let e₁ := Ext.homPlusAddEquiv (X := U) (Y := M) q
  let e₂ := (Linear.homCongr ℤ u.symm (Iso.refl (M₀⟦(q : ℤ)⟧))).toAddEquiv
  let e₃ := (moduleDerivedAdjunction Λ f).homAddEquiv I₀ (M₀⟦(q : ℤ)⟧)
  let e₄ := (Linear.homCongr ℤ (Iso.refl I₀) ((R.commShiftIso (q : ℤ)).app M₀)).toAddEquiv
  let e₅ := (s.homAddEquiv I₀ K).symm
  let e₆ := (Linear.homCongr ℤ t (Iso.refl K)).toAddEquiv
  let e₇ := moduleFieldDerivedUnitHomologyAddEquiv Ω Λ (q : ℤ) K
  unfold moduleFieldDirectImageHomologyAddEquiv
  change e₇.symm (e₇ (e₆ (e₅ (e₄ (e₃ (e₂ (e₁ x))))))) =
    t.inv ≫ (s.homEquiv I₀ K).symm
      ((moduleDerivedAdjunction Λ f).shiftedHomEquiv (q : ℤ) I₀ M₀ (u.hom ≫ x.homPlus))
  rw [e₇.symm_apply_apply]
  change (t.inv ≫ (s.homEquiv I₀ K).symm
    ((𝟙 I₀ ≫ (moduleDerivedAdjunction Λ f).homEquiv I₀ (M₀⟦(q : ℤ)⟧)
      ((u.hom ≫ x.homPlus) ≫ 𝟙 _)) ≫ (R.commShiftIso (q : ℤ)).hom.app M₀)) ≫ 𝟙 K =
    t.inv ≫ (s.homEquiv I₀ K).symm
      ((moduleDerivedAdjunction Λ f).shiftedHomEquiv (q : ℤ) I₀ M₀ (u.hom ≫ x.homPlus))
  simp only [Category.id_comp, Category.comp_id, Adjunction.shiftedHomEquiv_apply]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
