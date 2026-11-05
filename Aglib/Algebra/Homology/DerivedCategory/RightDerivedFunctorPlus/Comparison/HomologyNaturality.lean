/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.NaturalTransformation
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-! # Exact homology comparisons respect arbitrary coefficient transformations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]

omit [HasDerivedCategory.{wA} A] [EnoughInjectives A] [HasDerivedCategory.{wB} B] in
/-- The original termwise homology comparison is natural in the whole coefficient functor. -/
theorem mapCochainComplexPlusHomologyIso_naturality
    (α : F ⟶ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n).map
        ((NatTrans.mapCochainComplexPlus α).app K) ≫
      (G.mapCochainComplexPlusHomologyIso n).hom.app K =
    (F.mapCochainComplexPlusHomologyIso n).hom.app K ≫
      α.app ((CochainComplex.Plus.ι A ⋙
        HomologicalComplex.homologyFunctor A (.up ℤ) n).obj K) := by
  change ShortComplex.homologyMap ((K.obj.sc n).mapNatTrans α) ≫
      ((K.obj.sc n).mapHomologyIso G).hom =
    ((K.obj.sc n).mapHomologyIso F).hom ≫ α.app (K.obj.sc n).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Component normalization at an original complex, using the original derived units. -/
theorem rightDerivedFunctorPlusHomologyIso_naturality_Q
    (α : F ⟶ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.homologyFunctor B n).map
        ((F.rightDerivedFunctorPlusNatTrans α).app (DerivedCategory.Plus.Q.obj K)) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) =
    (F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      α.app ((DerivedCategory.Plus.homologyFunctor A n).obj (DerivedCategory.Plus.Q.obj K)) := by
  let HB := DerivedCategory.Plus.homologyFunctor B n
  let aA := DerivedCategory.Plus.homologyFunctorFactors (A := A) n
  let aB := DerivedCategory.Plus.homologyFunctorFactors (A := B) n
  let c := (NatTrans.mapCochainComplexPlus α).app K
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hd := congrArg HB.map (F.rightDerivedFunctorPlusNatTrans_app α K)
  simp only [Functor.map_comp] at hd
  have ha := aB.hom.naturality c
  change HB.map (DerivedCategory.Plus.Q.map c) ≫
      aB.hom.app (G.mapCochainComplexPlus.obj K) =
    aB.hom.app (F.mapCochainComplexPlus.obj K) ≫
      (CochainComplex.Plus.ι B ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n).map c at ha
  have hc := mapCochainComplexPlusHomologyIso_naturality α n K
  simp only [Functor.comp_map] at hc
  have hn := α.naturality (aA.hom.app K)
  simp only [Functor.comp_obj] at hn
  have hF := F.rightDerivedFunctorPlusHomologyIso_unit n K
  have hG := G.rightDerivedFunctorPlusHomologyIso_unit n K
  apply (cancel_epi (HB.map (F.rightDerivedFunctorPlusUnit.app K))).1
  apply (cancel_mono (G.map (aA.hom.app K))).1
  simp only [Category.assoc]
  rw [reassoc_of% hd, hG, reassoc_of% ha]
  dsimp only [c]
  rw [hc]
  erw [← hn]
  simpa only [HB, aA, aB, Category.assoc, Functor.comp_obj] using
    (congrArg (fun z => z ≫ α.app ((CochainComplex.Plus.ι A ⋙
      HomologicalComplex.homologyFunctor A (.up ℤ) n).obj K)) hF).symm

/-- The actual exact derived homology comparison is coefficient-natural on every object. -/
theorem rightDerivedFunctorPlusHomologyIso_naturality
    (α : F ⟶ G) (n : ℤ) :
    whiskerRight (F.rightDerivedFunctorPlusNatTrans α)
        (DerivedCategory.Plus.homologyFunctor B n) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom =
    (F.rightDerivedFunctorPlusHomologyIso n).hom ≫
      whiskerLeft (DerivedCategory.Plus.homologyFunctor A n) α := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
  intro K
  exact rightDerivedFunctorPlusHomologyIso_naturality_Q α n K

end CategoryTheory.Functor
