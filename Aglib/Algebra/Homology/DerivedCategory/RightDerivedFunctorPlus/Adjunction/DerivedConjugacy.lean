/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.CompositeUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComplexConjugacy
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

/-! # The actual derived adjunctions respect the installed composition comparisons -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction
open CategoryTheory.Functor
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [L₀.Additive] [R₀.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology] [L₀.PreservesHomology]
  [R₂.PreservesInjectiveObjects]

/-- The original conjugate composition comparisons remain the actual derived conjugate maps. -/
theorem rightDerivedFunctorPlus_conjugate_comp
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₀ : L₀ ⊣ R₀)
    (eL : L₀ ≅ L₁ ⋙ L₂) (eR : R₂ ⋙ R₁ ≅ R₀)
    (h : conjugateEquiv (adj₁.comp adj₂) adj₀ eL.hom = eR.hom) :
    conjugateEquiv (adj₁.rightDerivedFunctorPlus.comp adj₂.rightDerivedFunctorPlus)
        adj₀.rightDerivedFunctorPlus
        (L₀.rightDerivedFunctorPlusIso eL ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology L₁ L₂).hom =
      (R₀.rightDerivedFunctorPlusIso eR.symm ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives R₂ R₁).inv := by
  let QA : CochainComplex.Plus A ⥤ DerivedCategory.Plus A := DerivedCategory.Plus.Q
  let QB : CochainComplex.Plus B ⥤ DerivedCategory.Plus B := DerivedCategory.Plus.Q
  let QC : CochainComplex.Plus C ⥤ DerivedCategory.Plus C := DerivedCategory.Plus.Q
  let c : QA ⋙ (L₁.rightDerivedFunctorPlus ⋙ L₂.rightDerivedFunctorPlus) ≅
      (L₁.mapCochainComplexPlus ⋙ L₂.mapCochainComplexPlus) ⋙ QC :=
    (associator QA L₁.rightDerivedFunctorPlus L₂.rightDerivedFunctorPlus).symm ≪≫
      isoWhiskerRight L₁.rightDerivedFunctorPlusExactComparison L₂.rightDerivedFunctorPlus ≪≫
      associator L₁.mapCochainComplexPlus QB L₂.rightDerivedFunctorPlus ≪≫
      isoWhiskerLeft L₁.mapCochainComplexPlus L₂.rightDerivedFunctorPlusExactComparison ≪≫
      (associator L₁.mapCochainComplexPlus L₂.mapCochainComplexPlus QC).symm
  let r : (R₂.mapCochainComplexPlus ⋙ R₁.mapCochainComplexPlus) ⋙ QA ⟶
      QC ⋙ (R₂.rightDerivedFunctorPlus ⋙ R₁.rightDerivedFunctorPlus) :=
    (associator R₂.mapCochainComplexPlus R₁.mapCochainComplexPlus QA).hom ≫
      whiskerLeft R₂.mapCochainComplexPlus R₁.rightDerivedFunctorPlusUnit ≫
      (associator R₂.mapCochainComplexPlus QB R₁.rightDerivedFunctorPlus).inv ≫
      whiskerRight R₂.rightDerivedFunctorPlusUnit R₁.rightDerivedFunctorPlus ≫
      (associator QC R₂.rightDerivedFunctorPlus R₁.rightDerivedFunctorPlus).hom
  refine conjugateEquiv_eq_of_localization QA QC (CochainComplex.Plus.quasiIso A)
    (adj₁.mapCochainComplexPlus.comp adj₂.mapCochainComplexPlus) adj₀.mapCochainComplexPlus
    (adj₁.rightDerivedFunctorPlus.comp adj₂.rightDerivedFunctorPlus) adj₀.rightDerivedFunctorPlus
    c L₀.rightDerivedFunctorPlusExactComparison r R₀.rightDerivedFunctorPlusUnit
    _ _ _ _ (mapCochainComplexPlus_conjugate_comp adj₁ adj₂ adj₀ eL eR h) ?_ ?_ ?_ ?_
  · intro K
    have hu := unit_fac_comp QA QB QC adj₁.mapCochainComplexPlus adj₂.mapCochainComplexPlus
      adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus
      L₁.rightDerivedFunctorPlusExactComparison.hom L₂.rightDerivedFunctorPlusExactComparison.hom
      R₁.rightDerivedFunctorPlusUnit R₂.rightDerivedFunctorPlusUnit
      adj₁.rightDerivedFunctorPlus_unit_fac adj₂.rightDerivedFunctorPlus_unit_fac K
    simpa only [c, r, QA, QB, QC, Functor.comp_obj, Functor.map_id,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.comp_map, Functor.map_comp] using hu
  · exact adj₀.rightDerivedFunctorPlus_unit_fac
  · intro K
    simpa only [c, QA, QB, QC, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]
      using rightDerivedFunctorPlusCompIso_exactComparison_square L₁ L₂ L₀ eL K
  · intro K
    simpa only [r, QA, QB, QC, Functor.comp_obj, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]
      using rightDerivedFunctorPlusCompIso_originalUnit_square R₂ R₁ R₀ eR K

end CategoryTheory.Adjunction
