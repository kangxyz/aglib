/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Canonical comparison of two native bounded-below localizations

The compared realizations and their quotient maps remain independent. Only the
comparison data needed by target transport are named; native categories and
native quotient functors are used directly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Localization

variable {C D₀ D₁ : Type*} [Category* C] [Category* D₀] [Category* D₁]
  (L₀ : C ⥤ D₀) (L₁ : C ⥤ D₁) (W : MorphismProperty C)
  [L₀.IsLocalization W] [L₁.IsLocalization W]

/-- Localization uniqueness preserves the specified quotient comparison. -/
@[reassoc]
theorem isoUniqFunctor_hom_app_comp (F : D₀ ⥤ D₁) (e : L₀ ⋙ F ≅ L₁) (X : C) :
    (isoUniqFunctor L₀ L₁ W F e).hom.app (L₀.obj X) ≫
      (compUniqFunctor L₀ L₁ W).hom.app X = e.hom.app X := by
  simp [isoUniqFunctor, liftNatIso, liftNatTrans_app, Lifting.iso]

end CategoryTheory.Localization

namespace DerivedCategory.Plus

universe u v d₀ d₁ d₂
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Uniqueness of the two actual localizations at bounded-below quasi-isomorphisms. -/
def canonicalEquivalence (h₀ : HasDerivedCategory.{d₀} A)
    (h₁ : HasDerivedCategory.{d₁} A) :
    @DerivedCategory.Plus A _ _ h₀ ≌ @DerivedCategory.Plus A _ _ h₁ :=
  Localization.uniq (@DerivedCategory.Plus.Q A _ _ h₀)
    (@DerivedCategory.Plus.Q A _ _ h₁) (CochainComplex.Plus.quasiIso A)

/-- The actual quotient comparison that normalizes the canonical equivalence. -/
def quotientCompCanonicalEquivalenceIso (h₀ : HasDerivedCategory.{d₀} A)
    (h₁ : HasDerivedCategory.{d₁} A) :
    @DerivedCategory.Plus.Q A _ _ h₀ ⋙ (canonicalEquivalence h₀ h₁).functor ≅
      @DerivedCategory.Plus.Q A _ _ h₁ :=
  Localization.compUniqFunctor (@DerivedCategory.Plus.Q A _ _ h₀)
    (@DerivedCategory.Plus.Q A _ _ h₁) (CochainComplex.Plus.quasiIso A)

/-- Original homology factors through the selected native quotient. -/
def quotientHomologyIso (h : HasDerivedCategory.{d₀} A) (n : ℤ) :
    @DerivedCategory.Plus.Q A _ _ h ⋙ @DerivedCategory.Plus.homologyFunctor A _ _ h n ≅
      CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n := by
  letI := h
  exact (associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedCategory.Plus.QCompιIso A) _ ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors A n)

/-- Canonical target transport preserves original homology. -/
def canonicalEquivalenceHomologyIso (h₀ : HasDerivedCategory.{d₀} A)
    (h₁ : HasDerivedCategory.{d₁} A) (n : ℤ) :
    (canonicalEquivalence h₀ h₁).functor ⋙ @DerivedCategory.Plus.homologyFunctor A _ _ h₁ n ≅
      @DerivedCategory.Plus.homologyFunctor A _ _ h₀ n := by
  let L := @DerivedCategory.Plus.Q A _ _ h₀
  let F := CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n
  letI : Localization.Lifting L (CochainComplex.Plus.quasiIso A) F
      ((canonicalEquivalence h₀ h₁).functor ⋙ @DerivedCategory.Plus.homologyFunctor A _ _ h₁ n) :=
    ⟨(associator _ _ _).symm ≪≫
      isoWhiskerRight (quotientCompCanonicalEquivalenceIso h₀ h₁) _ ≪≫
      quotientHomologyIso h₁ n⟩
  letI : Localization.Lifting L (CochainComplex.Plus.quasiIso A) F
      (@DerivedCategory.Plus.homologyFunctor A _ _ h₀ n) := ⟨quotientHomologyIso h₀ n⟩
  exact Localization.liftNatIso L (CochainComplex.Plus.quasiIso A) F F _ _ (Iso.refl F)

/-- The self-comparison contracts through its original quotient unitor. -/
def canonicalEquivalenceIdIso (h₀ : HasDerivedCategory.{d₀} A) :
    (canonicalEquivalence h₀ h₀).functor ≅ 𝟭 (@DerivedCategory.Plus A _ _ h₀) :=
  (Localization.isoUniqFunctor (@DerivedCategory.Plus.Q A _ _ h₀)
    (@DerivedCategory.Plus.Q A _ _ h₀) (CochainComplex.Plus.quasiIso A)
    (𝟭 _) (rightUnitor _)).symm

/-- Canonical comparisons compose through the original two quotient comparisons. -/
def canonicalEquivalenceCompIso (h₀ : HasDerivedCategory.{d₀} A)
    (h₁ : HasDerivedCategory.{d₁} A) (h₂ : HasDerivedCategory.{d₂} A) :
    (canonicalEquivalence h₀ h₁).functor ⋙ (canonicalEquivalence h₁ h₂).functor ≅
      (canonicalEquivalence h₀ h₂).functor :=
  Localization.isoUniqFunctor (@DerivedCategory.Plus.Q A _ _ h₀)
    (@DerivedCategory.Plus.Q A _ _ h₂) (CochainComplex.Plus.quasiIso A) _
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (quotientCompCanonicalEquivalenceIso h₀ h₁) _ ≪≫
      quotientCompCanonicalEquivalenceIso h₁ h₂)

end DerivedCategory.Plus
