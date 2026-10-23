/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-! # Unit coherence of the installed bounded-below composition comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w'
namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] [EnoughInjectives B]
  (F : A ⥤ B) [F.Additive]

omit [EnoughInjectives B] in
/-- The injective-preserving comparison respects the original left unitor. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_leftUnitor :
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives (𝟭 A) F ≪≫
        isoWhiskerRight (rightDerivedFunctorPlusIdIso A) F.rightDerivedFunctorPlus ≪≫
        leftUnitor F.rightDerivedFunctorPlus =
      (𝟭 A ⋙ F).rightDerivedFunctorPlusIso (leftUnitor F) := by
  apply Iso.ext
  apply (𝟭 A ⋙ F).rightDerivedFunctorPlus.rightDerived_ext
    (𝟭 A ⋙ F).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom,
    isoWhiskerRight_hom, whiskerRight_app, leftUnitor_hom_app, comp_obj]
  change (𝟭 A ⋙ F).rightDerivedFunctorPlusUnit.app K ≫
      ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives (𝟭 A) F).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
        (F.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusIdIso A).hom.app (DerivedCategory.Plus.Q.obj K)) ≫ 𝟙 _)) = _
  rw [Category.comp_id]
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
    Category.assoc, ← F.rightDerivedFunctorPlus.map_comp, rightDerivedFunctorPlusIdIso_unit,
    rightDerivedFunctorPlusIso_hom_app]
  have hm : (NatIso.mapCochainComplexPlus (leftUnitor F)).hom.app K =
      F.mapCochainComplexPlus.map ((mapCochainComplexPlusIdIso A).hom.app K) := by
    apply ObjectProperty.hom_ext
    ext n
    change 𝟙 (F.obj (K.obj.X n)) = F.map (𝟙 (K.obj.X n))
    exact (F.map_id _).symm
  rw [hm]
  simpa only [comp_map, comp_obj, id_obj] using
    (F.rightDerivedFunctorPlusUnit.naturality ((mapCochainComplexPlusIdIso A).hom.app K)).symm

/-- The homology-preserving comparison respects the original right unitor. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_rightUnitor :
    rightDerivedFunctorPlusCompIsoOfPreservesHomology F (𝟭 B) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso B) ≪≫
        rightUnitor F.rightDerivedFunctorPlus =
      (F ⋙ 𝟭 B).rightDerivedFunctorPlusIso (rightUnitor F) := by
  apply Iso.ext
  apply (F ⋙ 𝟭 B).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ 𝟭 B).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom,
    isoWhiskerLeft_hom, rightUnitor_hom_app, comp_obj]
  change (F ⋙ 𝟭 B).rightDerivedFunctorPlusUnit.app K ≫
      ((rightDerivedFunctorPlusCompIsoOfPreservesHomology F (𝟭 B)).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
        ((rightDerivedFunctorPlusIdIso B).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫ 𝟙 _)) = _
  rw [Category.comp_id]
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    Category.assoc]
  have hn := congrArg
    (fun t => (𝟭 B).rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫ t)
    ((rightDerivedFunctorPlusIdIso B).hom.naturality (F.rightDerivedFunctorPlusUnit.app K))
  simp only [comp_obj, id_map] at hn
  conv_rhs at hn => rw [← Category.assoc, rightDerivedFunctorPlusIdIso_unit]
  rw [hn, rightDerivedFunctorPlusIso_hom_app]
  congr 2

end CategoryTheory.Functor
