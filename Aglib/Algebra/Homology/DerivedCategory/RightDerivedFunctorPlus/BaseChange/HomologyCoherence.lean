/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityConjugacy
public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-! # Original exact homology comparison factors and complex coherence -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits
namespace CategoryTheory
universe uA vA wA uB vB wB uC vC wC
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Native homology preservation for the identity is literally the identity map. -/
theorem ShortComplex.mapHomologyIso_id_hom (S : ShortComplex A) :
    (S.mapHomologyIso (𝟭 A)).hom = 𝟙 S.homology := by
  have h := ShortComplex.mapHomologyIso_comp_hom (𝟭 A) (𝟭 A) S
  change (S.mapHomologyIso (𝟭 A)).hom =
    (S.mapHomologyIso (𝟭 A)).hom ≫ (S.mapHomologyIso (𝟭 A)).hom at h
  apply (cancel_epi (S.mapHomologyIso (𝟭 A)).hom).mp
  exact h.symm.trans (Category.comp_id (S.mapHomologyIso (𝟭 A)).hom).symm

namespace Functor
variable [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B] [HasDerivedCategory.{wC} C]

omit [EnoughInjectives B] in
/-- The native homology comparison factors through the actual exact comparison. -/
theorem rightDerivedFunctorPlusHomologyIso_exactComparison
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (n : ℤ) (K : CochainComplex.Plus A) :
    (F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).hom.app K) =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).hom.app
          (F.mapCochainComplexPlus.obj K) ≫
        (F.mapCochainComplexPlusHomologyIso n).hom.app K := by
  apply (cancel_epi ((DerivedCategory.Plus.homologyFunctor B n).map
    (F.rightDerivedFunctorPlusExactComparison.inv.app K))).mp
  rw [rightDerivedFunctorPlusExactComparison_inv_app]
  rw [F.rightDerivedFunctorPlusHomologyIso_unit]
  rw [← Functor.map_comp_assoc]
  change _ = (DerivedCategory.Plus.homologyFunctor B n).map
    (F.rightDerivedFunctorPlusExactComparison.inv.app K ≫
      F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫ _
  rw [Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]

omit [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B] [HasDerivedCategory.{wC} C] in
/-- The termwise homology comparisons respect the actual specified composition. -/
theorem mapCochainComplexPlusHomologyIso_comp
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : H ≅ F ⋙ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n).map
        ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app K) ≫
      (G.mapCochainComplexPlusHomologyIso n).hom.app (F.mapCochainComplexPlus.obj K) ≫
      G.map ((F.mapCochainComplexPlusHomologyIso n).hom.app K) =
    (H.mapCochainComplexPlusHomologyIso n).hom.app K ≫ e.hom.app (K.obj.homology n) := by
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_preservesHomology F
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_preservesHomology F
  let : PreservesFiniteLimits G := preservesFiniteLimits_of_preservesHomology G
  let : PreservesFiniteColimits G := preservesFiniteColimits_of_preservesHomology G
  have he : (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app K := by
    simp [mapCochainComplexPlusCompIso]
  rw [he]
  change ShortComplex.homologyMap ((K.obj.sc n).mapNatTrans e.hom) ≫
      (((K.obj.sc n).map F).mapHomologyIso G).hom ≫
        G.map ((K.obj.sc n).mapHomologyIso F).hom =
    ((K.obj.sc n).mapHomologyIso H).hom ≫ e.hom.app (K.obj.sc n).homology
  rw [← ShortComplex.mapHomologyIso_comp_hom F G,
    ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [HasDerivedCategory.{wA} A] [EnoughInjectives A] in
/-- The termwise homology comparison respects a specified identity comparison. -/
theorem mapCochainComplexPlusHomologyIso_id
    (F : A ⥤ A) [F.Additive] [F.PreservesHomology]
    (e : F ≅ 𝟭 A) (n : ℤ) (K : CochainComplex.Plus A) :
    (CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n).map
        ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app K) =
      (F.mapCochainComplexPlusHomologyIso n).hom.app K ≫ e.hom.app (K.obj.homology n) := by
  have he : (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app K := by
    simp [mapCochainComplexPlusIdIso]
  rw [he]
  change ShortComplex.homologyMap ((K.obj.sc n).mapNatTrans e.hom) =
    ((K.obj.sc n).mapHomologyIso F).hom ≫ e.hom.app (K.obj.sc n).homology
  have hn := congrArg (fun z => z ≫ ((K.obj.sc n).mapHomologyIso (𝟭 A)).hom)
    (ShortComplex.homologyMap_mapNatTrans (K.obj.sc n) e.hom)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hn
  rw [ShortComplex.mapHomologyIso_id_hom] at hn
  exact (Category.comp_id (ShortComplex.homologyMap
    ((K.obj.sc n).mapNatTrans e.hom))).symm.trans hn

-- Append in namespace CategoryTheory.Functor after HomologyComparisonFactors.

/-- Native homology composition coherence first on localized actual complexes. -/
theorem rightDerivedFunctorPlusHomologyIso_comp_Q
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : H ≅ F ⋙ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        ((H.rightDerivedFunctorPlusIso e ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
            (DerivedCategory.Plus.Q.obj K)) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      G.map ((F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K)) =
    (H.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      e.hom.app ((DerivedCategory.Plus.homologyFunctor A n).obj
        (DerivedCategory.Plus.Q.obj K)) := by
  let HA := DerivedCategory.Plus.homologyFunctor A n
  let HB := DerivedCategory.Plus.homologyFunctor B n
  let HC := DerivedCategory.Plus.homologyFunctor C n
  let aA := DerivedCategory.Plus.homologyFunctorFactors (A := A) n
  let aB := DerivedCategory.Plus.homologyFunctorFactors (A := B) n
  let aC := DerivedCategory.Plus.homologyFunctorFactors (A := C) n
  let c := (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app K
  let d := (H.rightDerivedFunctorPlusIso e ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app (DerivedCategory.Plus.Q.obj K)
  have hn := (G.rightDerivedFunctorPlusHomologyIso n).hom.naturality
    (F.rightDerivedFunctorPlusExactComparison.hom.app K)
  change HC.map (G.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusExactComparison.hom.app K)) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom.app
        (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) =
    (G.rightDerivedFunctorPlusHomologyIso n).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      G.map (HB.map (F.rightDerivedFunctorPlusExactComparison.hom.app K)) at hn
  have he := congrArg HC.map
    (rightDerivedFunctorPlusCompIso_exactComparison_square F G H e K)
  simp only [Functor.map_comp] at he
  have ha := aC.hom.naturality c
  change HC.map (DerivedCategory.Plus.Q.map c) ≫
      aC.hom.app (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K)) =
    aC.hom.app (H.mapCochainComplexPlus.obj K) ≫
      (CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) n).map c at ha
  have hc := mapCochainComplexPlusHomologyIso_comp F G H e n K
  have hF := rightDerivedFunctorPlusHomologyIso_exactComparison F n K
  have hG := rightDerivedFunctorPlusHomologyIso_exactComparison G n (F.mapCochainComplexPlus.obj K)
  have hH := rightDerivedFunctorPlusHomologyIso_exactComparison H n K
  have hE := e.hom.naturality (aA.hom.app K)
  change H.map (aA.hom.app K) ≫ e.hom.app (K.obj.homology n) =
    e.hom.app (HA.obj (DerivedCategory.Plus.Q.obj K)) ≫ G.map (F.map (aA.hom.app K)) at hE
  apply (cancel_mono (G.map (F.map (aA.hom.app K)))).mp
  simp only [Category.assoc]
  rw [← G.map_comp, hF, G.map_comp, G.map_comp]
  rw [← reassoc_of% hn]
  rw [reassoc_of% hG]
  rw [reassoc_of% he]
  rw [reassoc_of% ha]
  simp only [Functor.comp_map] at hc
  dsimp only [c]
  rw [hc]
  rw [← hE]
  simpa only [HC, aA, aC, Category.assoc] using
    (congrArg (fun z => z ≫ e.hom.app (K.obj.homology n)) hH).symm

/-- The actual homology comparisons respect a specified transported composition. -/
theorem rightDerivedFunctorPlusHomologyIso_comp
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : H ≅ F ⋙ G) (n : ℤ) (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor C n).map
        ((H.rightDerivedFunctorPlusIso e ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app K) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom.app (F.rightDerivedFunctorPlus.obj K) ≫
      G.map ((F.rightDerivedFunctorPlusHomologyIso n).hom.app K) =
    (H.rightDerivedFunctorPlusHomologyIso n).hom.app K ≫
      e.hom.app ((DerivedCategory.Plus.homologyFunctor A n).obj K) := by
  let lhs := isoWhiskerRight (H.rightDerivedFunctorPlusIso e ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F G)
      (DerivedCategory.Plus.homologyFunctor C n) ≪≫
    associator _ _ _ ≪≫ isoWhiskerLeft F.rightDerivedFunctorPlus
      (G.rightDerivedFunctorPlusHomologyIso n) ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (F.rightDerivedFunctorPlusHomologyIso n) G ≪≫ associator _ _ _
  let rhs := H.rightDerivedFunctorPlusHomologyIso n ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor A n) e
  have he : lhs.hom = rhs.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
    intro J
    simpa only [lhs, rhs, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, associator_inv_app, Functor.comp_obj,
      Category.id_comp, Category.comp_id, Category.assoc]
      using rightDerivedFunctorPlusHomologyIso_comp_Q F G H e n J
  simpa only [lhs, rhs, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Functor.comp_obj,
    Category.id_comp, Category.comp_id, Category.assoc] using congr_app he K

/-- The native homology identity law on localized actual complexes. -/
theorem rightDerivedFunctorPlusHomologyIso_id_Q
    (F : A ⥤ A) [F.Additive] [F.PreservesHomology]
    (e : F ≅ 𝟭 A) (n : ℤ) (K : CochainComplex.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A n).map
        ((F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
          (DerivedCategory.Plus.Q.obj K)) =
      (F.rightDerivedFunctorPlusHomologyIso n).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        e.hom.app ((DerivedCategory.Plus.homologyFunctor A n).obj
          (DerivedCategory.Plus.Q.obj K)) := by
  let Hq := DerivedCategory.Plus.homologyFunctor A n
  let a := DerivedCategory.Plus.homologyFunctorFactors (A := A) n
  let c := (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app K
  have ha := a.hom.naturality c
  change Hq.map (DerivedCategory.Plus.Q.map c) ≫ a.hom.app K =
    a.hom.app (F.mapCochainComplexPlus.obj K) ≫
      (CochainComplex.Plus.ι A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n).map c at ha
  have hE := e.hom.naturality (a.hom.app K)
  change F.map (a.hom.app K) ≫ e.hom.app (K.obj.homology n) =
    e.hom.app (Hq.obj (DerivedCategory.Plus.Q.obj K)) ≫ a.hom.app K at hE
  apply (cancel_mono (a.hom.app K)).mp
  rw [rightDerivedFunctorPlusIso_id_exactComparison, Functor.map_comp, Category.assoc]
  rw [ha, mapCochainComplexPlusHomologyIso_id]
  rw [← reassoc_of% (rightDerivedFunctorPlusHomologyIso_exactComparison F n K)]
  simp only [Category.assoc]
  rw [hE]

/-- The actual homology comparison respects a specified transported identity. -/
theorem rightDerivedFunctorPlusHomologyIso_id
    (F : A ⥤ A) [F.Additive] [F.PreservesHomology]
    (e : F ≅ 𝟭 A) (n : ℤ) (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor A n).map
        ((F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app K) =
      (F.rightDerivedFunctorPlusHomologyIso n).hom.app K ≫
        e.hom.app ((DerivedCategory.Plus.homologyFunctor A n).obj K) := by
  let lhs := isoWhiskerRight (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A)
      (DerivedCategory.Plus.homologyFunctor A n) ≪≫ leftUnitor _
  let rhs := F.rightDerivedFunctorPlusHomologyIso n ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor A n) e ≪≫ rightUnitor _
  have he : lhs.hom = rhs.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
    intro J
    simpa only [lhs, rhs, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      leftUnitor_hom_app, rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id] using rightDerivedFunctorPlusHomologyIso_id_Q F e n J
  simpa only [lhs, rhs, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app, rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id] using congr_app he K

end Functor
end CategoryTheory
