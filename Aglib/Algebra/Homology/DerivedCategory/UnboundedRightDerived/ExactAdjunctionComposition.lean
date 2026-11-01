/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAdjunction
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.CompositeUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.LocalizedConjugacy

/-! # The actual derived adjunctions respect the installed composition comparisons -/

@[expose] public section
noncomputable section

namespace CategoryTheory.Adjunction
open CategoryTheory.Functor CategoryTheory.Limits
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [L₀.Additive] [R₀.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]

private theorem exactAdjunction_unit_fac {L : A ⥤ B} {R : B ⥤ A}
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (K : CochainComplex A ℤ) :
    a.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) := by
  have h := unit_mateEquiv (a.mapHomologicalComplex (.up ℤ)) a.mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _ L.mapDerivedCategoryFactors.hom) K
  change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    (mateEquiv (a.mapHomologicalComplex (.up ℤ)) a.mapDerivedCategoryAdjunction
      (TwoSquare.mk _ _ _ _ L.mapDerivedCategoryFactors.hom)).natTrans.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K) = _ at h
  rw [a.mapDerivedCategoryAdjunction_factor_mate] at h
  exact h.symm

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀] in
private theorem mapComplex_conjugate_comp
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₀ ⊣ R₀)
    (eL : L₀ ≅ L₁ ⋙ L₂) (eR : R₂ ⋙ R₁ ≅ R₀)
    (h : conjugateEquiv (a.comp b) c eL.hom = eR.hom) :
    conjugateEquiv ((a.mapHomologicalComplex (.up ℤ)).comp
        (b.mapHomologicalComplex (.up ℤ))) (c.mapHomologicalComplex (.up ℤ))
        (NatIso.mapHomologicalComplex eL (.up ℤ)).hom =
      (NatIso.mapHomologicalComplex eR (.up ℤ)).hom := by
  apply conjugateEquiv_eq_of_unit
  ext K n
  have hu := unit_conjugateEquiv (a.comp b) c eL.hom (K.X n)
  rw [h] at hu
  exact hu

/-- The original conjugate composition comparisons remain the actual derived conjugate maps. -/
theorem mapDerivedCategory_conjugate_comp
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₀ : L₀ ⊣ R₀)
    (eL : L₀ ≅ L₁ ⋙ L₂) (eR : R₂ ⋙ R₁ ≅ R₀)
    (h : conjugateEquiv (adj₁.comp adj₂) adj₀ eL.hom = eR.hom) :
    conjugateEquiv (adj₁.mapDerivedCategoryAdjunction.comp adj₂.mapDerivedCategoryAdjunction)
        adj₀.mapDerivedCategoryAdjunction
        (mapDerivedCategoryCompositeIso L₁ L₂ L₀ eL).hom =
      (mapDerivedCategoryCompositeIso R₂ R₁ R₀ eR.symm).inv := by
  let QA : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let QC : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let c : QA ⋙ (L₁.mapDerivedCategory ⋙ L₂.mapDerivedCategory) ≅
      ((L₁.mapHomologicalComplex (.up ℤ)) ⋙ (L₂.mapHomologicalComplex (.up ℤ))) ⋙ QC :=
    (associator QA L₁.mapDerivedCategory L₂.mapDerivedCategory).symm ≪≫
      isoWhiskerRight L₁.mapDerivedCategoryFactors L₂.mapDerivedCategory ≪≫
      associator (L₁.mapHomologicalComplex (.up ℤ)) QB L₂.mapDerivedCategory ≪≫
      isoWhiskerLeft (L₁.mapHomologicalComplex (.up ℤ)) L₂.mapDerivedCategoryFactors ≪≫
      (associator (L₁.mapHomologicalComplex (.up ℤ)) (L₂.mapHomologicalComplex (.up ℤ)) QC).symm
  let r : ((R₂.mapHomologicalComplex (.up ℤ)) ⋙ (R₁.mapHomologicalComplex (.up ℤ))) ⋙ QA ⟶
      QC ⋙ (R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory) :=
    (associator (R₂.mapHomologicalComplex (.up ℤ)) (R₁.mapHomologicalComplex (.up ℤ)) QA).hom ≫
      whiskerLeft (R₂.mapHomologicalComplex (.up ℤ)) R₁.mapDerivedCategoryFactors.inv ≫
      (associator (R₂.mapHomologicalComplex (.up ℤ)) QB R₁.mapDerivedCategory).inv ≫
      whiskerRight R₂.mapDerivedCategoryFactors.inv R₁.mapDerivedCategory ≫
      (associator QC R₂.mapDerivedCategory R₁.mapDerivedCategory).hom
  refine conjugateEquiv_eq_of_localization QA QC (HomologicalComplex.quasiIso A (.up ℤ))
    ((adj₁.mapHomologicalComplex (.up ℤ)).comp (adj₂.mapHomologicalComplex (.up ℤ)))
      (adj₀.mapHomologicalComplex (.up ℤ))
    (adj₁.mapDerivedCategoryAdjunction.comp adj₂.mapDerivedCategoryAdjunction)
      adj₀.mapDerivedCategoryAdjunction
    c L₀.mapDerivedCategoryFactors r R₀.mapDerivedCategoryFactors.inv
    _ _ _ _ (mapComplex_conjugate_comp adj₁ adj₂ adj₀ eL eR h) ?_ ?_ ?_ ?_
  · intro K
    have hu := unit_fac_comp QA QB QC (adj₁.mapHomologicalComplex (.up ℤ))
      (adj₂.mapHomologicalComplex (.up ℤ))
      adj₁.mapDerivedCategoryAdjunction adj₂.mapDerivedCategoryAdjunction
      L₁.mapDerivedCategoryFactors.hom L₂.mapDerivedCategoryFactors.hom
      R₁.mapDerivedCategoryFactors.inv R₂.mapDerivedCategoryFactors.inv
      (exactAdjunction_unit_fac adj₁) (exactAdjunction_unit_fac adj₂) K
    simpa only [c, r, QA, QB, QC, Functor.comp_obj, Functor.map_id,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.comp_map, Functor.map_comp] using hu
  · exact exactAdjunction_unit_fac adj₀
  · intro K
    simpa only [c, QA, QB, QC, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id]
      using mapDerivedCategoryCompositeIso_fac L₁ L₂ L₀ eL K
  · intro K
    have hc := mapDerivedCategoryCompositeIso_fac R₂ R₁ R₀ eR.symm K
    let E := mapDerivedCategoryCompositeIso R₂ R₁ R₀ eR.symm
    have hi : E.inv.app (DerivedCategory.Q.obj K) ≫ R₀.mapDerivedCategoryFactors.hom.app K =
        R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.hom.app K) ≫
          R₁.mapDerivedCategoryFactors.hom.app ((R₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app K) := by
      apply (cancel_epi (E.hom.app (DerivedCategory.Q.obj K))).mp
      rw [Iso.hom_inv_id_app_assoc]
      have hc' := congrArg (fun z => z ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app K)) hc
      simp only [Category.assoc] at hc'
      change _ = R₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).inv.app K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app K) at hc'
      rw [← Functor.map_comp, Iso.inv_hom_id_app] at hc'
      rw [DerivedCategory.Q.map_id] at hc'
      have hc'' := hc'.trans (Category.comp_id (R₀.mapDerivedCategoryFactors.hom.app K))
      simpa only [Category.assoc] using hc''.symm
    apply (cancel_mono (R₀.mapDerivedCategoryFactors.hom.app K)).mp
    simp only [r, QA, QB, QC, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.comp_obj, Category.assoc]
    rw [hi]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [R₁.mapDerivedCategory.map_id
      (((R₂.mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q).obj K)]
    exact (congrArg (fun z => R₁.mapDerivedCategoryFactors.inv.app
      ((R₂.mapHomologicalComplex (.up ℤ)).obj K) ≫ z)
      (Category.id_comp (R₁.mapDerivedCategoryFactors.hom.app
        ((R₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app K)))).trans
      ((R₁.mapDerivedCategoryFactors.inv_hom_id_app_assoc
        ((R₂.mapHomologicalComplex (.up ℤ)).obj K) _).trans (Category.comp_id _).symm)

end CategoryTheory.Adjunction
