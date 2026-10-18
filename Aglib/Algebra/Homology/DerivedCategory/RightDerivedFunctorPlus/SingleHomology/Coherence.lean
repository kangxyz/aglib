/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Exact-single and homology comparison coherence

Both native comparisons for the derived functor of an exact functor use its
installed derived unit. On a single complex their homology components agree
with the original single-complex identification. This equation is used when
lifting the higher-image open trace square to its original derived arrow.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v' w w'

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- The original exact-single complex map has its native homology component. -/
theorem singleMapHomologicalComplex_homology (n : ℤ) (M : A) :
    homologyMap ((singleMapHomologicalComplex F (.up ℤ) n).hom.app M) n ≫
        (singleObjHomologySelfIso (.up ℤ) n (F.obj M)).hom =
      ((((single A (.up ℤ) n).obj M).sc n).mapHomologyIso F).hom ≫
        F.map (singleObjHomologySelfIso (.up ℤ) n M).hom := by
  let K := (single A (.up ℤ) n).obj M
  let L := (F.mapHomologicalComplex (.up ℤ)).obj K
  let f := (singleMapHomologicalComplex F (.up ℤ) n).hom.app M
  have hπ : L.homologyπ n ≫ ((K.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) :=
    CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom F (K.sc n)
  have hi : cyclesMap f n ≫ ((single B (.up ℤ) n).obj (F.obj M)).iCycles n =
      L.iCycles n ≫ f.f n := HomologicalComplex.cyclesMap_i f n
  have hF : ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) = L.iCycles n :=
    (K.sc n).mapCyclesIso_hom_iCycles F
  have hc : cyclesMap f n ≫ (singleObjCyclesSelfIso (.up ℤ) n (F.obj M)).hom =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (singleObjCyclesSelfIso (.up ℤ) n M).hom := by
    simp only [singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, F.map_comp,
      ← Category.assoc]
    rw [hi, hF]
    simp only [f, singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (L.homologyπ n)).mp
  calc
    L.homologyπ n ≫ (homologyMap f n ≫
        (singleObjHomologySelfIso (.up ℤ) n (F.obj M)).hom) =
        cyclesMap f n ≫ (singleObjCyclesSelfIso (.up ℤ) n (F.obj M)).hom := by
      rw [homologyπ_naturality_assoc]
      dsimp only [Functor.comp_obj]
      rw [homologyπ_singleObjHomologySelfIso_hom]
    _ = ((K.sc n).mapCyclesIso F).hom ≫
        F.map (singleObjCyclesSelfIso (.up ℤ) n M).hom := hc
    _ = L.homologyπ n ≫ (((K.sc n).mapHomologyIso F).hom ≫
        F.map (singleObjHomologySelfIso (.up ℤ) n M).hom) := by
      rw [← Category.assoc, hπ, Category.assoc, ← F.map_comp]
      exact congrArg (fun z => ((K.sc n).mapCyclesIso F).hom ≫ F.map z)
        (homologyπ_singleObjHomologySelfIso_hom (.up ℤ) n M).symm

end HomologicalComplex

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

private theorem singleHomology_comparison
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D] (n : ℤ) (M : D) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D n).hom.app M =
      (DerivedCategory.Plus.homologyFunctorFactors (A := D) n).hom.app
        ((CochainComplex.singleFunctorPlus D n).obj M) ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n M).hom := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.Plus.homologyFunctorFactors,
    DerivedCategory.singleFunctorsPostcompQIso, DerivedCategory.Plus.QCompιIso,
    ObjectProperty.liftCompιIso]
  let Z := (HomologicalComplex.single D (.up ℤ) n).obj M
  let V := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor D n
  let h := (DerivedCategory.homologyFunctorFactors D n).hom.app Z
  let e := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n M).hom
  change H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h ≫ e =
    (𝟙 (H.obj V) ≫ H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h) ≫ e
  simp only [Functor.map_id, Category.id_comp]

/-- Homology of the installed exact-single comparison is the installed exact
homology comparison followed by the original single-homology identification. -/
theorem rightDerivedFunctorPlusSingleIso_homology (n : ℤ) (M : A) :
    (DerivedCategory.Plus.homologyFunctor B n).map
        ((F.rightDerivedFunctorPlusSingleIso n).hom.app M) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app (F.obj M) =
    (F.rightDerivedFunctorPlusHomologyIso n).hom.app
        ((DerivedCategory.Plus.singleFunctor A n).obj M) ≫
      F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).hom.app M) := by
  let K := (CochainComplex.singleFunctorPlus A n).obj M
  let σ : F.mapCochainComplexPlus.obj K ⟶
      (CochainComplex.singleFunctorPlus B n).obj (F.obj M) :=
    ObjectProperty.homMk
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app M)
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let HB := DerivedCategory.Plus.homologyFunctor B n
  let FA := DerivedCategory.Plus.homologyFunctorFactors (A := A) n
  let FB := DerivedCategory.Plus.homologyFunctorFactors (A := B) n
  have hunit := F.rightDerivedFunctorPlusHomologyIso_unit n K
  change HB.map (F.rightDerivedFunctorPlusUnit.app K) ≫
    (F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      F.map (FA.hom.app K) = FB.hom.app (F.mapCochainComplexPlus.obj K) ≫
        ((K.obj.sc n).mapHomologyIso F).hom at hunit
  have hσ := FB.hom.naturality σ
  change HB.map (DerivedCategory.Plus.Q.map σ) ≫
    FB.hom.app ((CochainComplex.singleFunctorPlus B n).obj (F.obj M)) =
    FB.hom.app (F.mapCochainComplexPlus.obj K) ≫ homologyMap σ.hom n at hσ
  have hsingle := congrArg (fun z => HB.map z)
    (F.rightDerivedFunctorPlusSingleIso_unit n M)
  simp only [Functor.map_comp] at hsingle
  apply (cancel_epi (HB.map (F.rightDerivedFunctorPlusUnit.app K))).mp
  calc
    HB.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (HB.map ((F.rightDerivedFunctorPlusSingleIso n).hom.app M) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app (F.obj M)) =
        HB.map (DerivedCategory.Plus.Q.map σ) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app (F.obj M) := by
      simpa only [Category.assoc, HB, K, σ] using
        congrArg (fun z => z ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso B n).hom.app (F.obj M)) hsingle
    _ = FB.hom.app (F.mapCochainComplexPlus.obj K) ≫
        (homologyMap σ.hom n ≫ (singleObjHomologySelfIso (.up ℤ) n (F.obj M)).hom) := by
      rw [singleHomology_comparison, ← Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (singleObjHomologySelfIso (.up ℤ) n (F.obj M)).hom) hσ
    _ = FB.hom.app (F.mapCochainComplexPlus.obj K) ≫
        (((K.obj.sc n).mapHomologyIso F).hom ≫
          F.map (singleObjHomologySelfIso (.up ℤ) n M).hom) := by
      convert congrArg (fun z => FB.hom.app (F.mapCochainComplexPlus.obj K) ≫ z)
        (HomologicalComplex.singleMapHomologicalComplex_homology F n M) using 1 <;> rfl
    _ = HB.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        ((F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
          F.map (FA.hom.app K) ≫ F.map (singleObjHomologySelfIso (.up ℤ) n M).hom) := by
      have hh := (congrArg (fun z => z ≫
        F.map (singleObjHomologySelfIso (.up ℤ) n M).hom) hunit).symm
      simpa only [Category.assoc] using hh
    _ = HB.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        ((F.rightDerivedFunctorPlusHomologyIso n).hom.app
            ((DerivedCategory.Plus.singleFunctor A n).obj M) ≫
          F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).hom.app M)) := by
      rw [singleHomology_comparison, F.map_comp]
      rfl

end CategoryTheory.Functor
