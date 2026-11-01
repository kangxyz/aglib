/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Grothendieck

/-! # Original unbounded derived units under a change of target localization

The source model is fixed. The two target models and their original quotient
functors are explicit, including when their size universes coincide. The
comparison is the native right-derived uniqueness map, not a chosen replacement.
-/

@[expose] public noncomputable section

open CategoryTheory

universe s u v w u' v' w₀ w₁

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  (hC : HasDerivedCategory.{w} C)
  (hD₀ : HasDerivedCategory.{w₀} D) (hD₁ : HasDerivedCategory.{w₁} D)

/-- The actual unbounded functor with its two native models explicitly supplied. -/
abbrev unboundedRightDerivedFunctorModel :
    @DerivedCategory C _ _ hC ⥤ @DerivedCategory D _ _ hD₀ := by
  letI := hC
  letI := hD₀
  exact F.unboundedRightDerivedFunctor

/-- The original unit in the specified native models. -/
abbrev unboundedRightDerivedFunctorModelUnit :
    F.mapHomologicalComplex (.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD₀ ⟶
      @DerivedCategory.Q C _ _ hC ⋙ F.unboundedRightDerivedFunctorModel hC hD₀ := by
  letI := hC
  letI := hD₀
  exact F.unboundedRightDerivedFunctorUnit

/-- The canonical comparison for the actual functor under target-model transport. -/
def unboundedRightDerivedFunctorChangeTarget :
    F.unboundedRightDerivedFunctorModel hC hD₀ ⋙
      (Localization.uniq (@DerivedCategory.Q D _ _ hD₀) (@DerivedCategory.Q D _ _ hD₁)
        (HomologicalComplex.quasiIso D (.up ℤ))).functor ≅
      F.unboundedRightDerivedFunctorModel hC hD₁ := by
  letI := hC
  exact rightDerivedNatIso _ _
    (whiskerRight (F.unboundedRightDerivedFunctorModelUnit hC hD₀) _ ≫
      (associator _ _ _).hom)
    (F.unboundedRightDerivedFunctorModelUnit hC hD₁)
    (HomologicalComplex.quasiIso C (.up ℤ))
    (associator _ _ _ ≪≫ isoWhiskerLeft _
      (Localization.compUniqFunctor (@DerivedCategory.Q D _ _ hD₀)
        (@DerivedCategory.Q D _ _ hD₁) (HomologicalComplex.quasiIso D (.up ℤ))))

/-- Target transport preserves the actual unit and original localization comparison. -/
@[reassoc]
theorem unboundedRightDerivedFunctorChangeTarget_unit (K : CochainComplex C ℤ) :
    (Localization.uniq (@DerivedCategory.Q D _ _ hD₀) (@DerivedCategory.Q D _ _ hD₁)
        (HomologicalComplex.quasiIso D (.up ℤ))).functor.map
        ((F.unboundedRightDerivedFunctorModelUnit hC hD₀).app K) ≫
      (F.unboundedRightDerivedFunctorChangeTarget hC hD₀ hD₁).hom.app
        ((@DerivedCategory.Q C _ _ hC).obj K) =
    (Localization.compUniqFunctor (@DerivedCategory.Q D _ _ hD₀)
        (@DerivedCategory.Q D _ _ hD₁) (HomologicalComplex.quasiIso D (.up ℤ))).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (F.unboundedRightDerivedFunctorModelUnit hC hD₁).app K := by
  let := hC
  have h := rightDerivedNatTrans_app _ _
    (whiskerRight (F.unboundedRightDerivedFunctorModelUnit hC hD₀) _ ≫
      (associator _ _ _).hom)
    (F.unboundedRightDerivedFunctorModelUnit hC hD₁)
    (HomologicalComplex.quasiIso C (.up ℤ))
    (associator _ _ _ ≪≫ isoWhiskerLeft _
      (Localization.compUniqFunctor (@DerivedCategory.Q D _ _ hD₀)
        (@DerivedCategory.Q D _ _ hD₁) (HomologicalComplex.quasiIso D (.up ℤ)))).hom K
  simpa only [unboundedRightDerivedFunctorChangeTarget, rightDerivedNatIso_hom,
    NatTrans.comp_app, whiskerRight_app, associator_hom_app, Category.comp_id,
    Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_app, Category.id_comp] using h

end CategoryTheory.Functor
