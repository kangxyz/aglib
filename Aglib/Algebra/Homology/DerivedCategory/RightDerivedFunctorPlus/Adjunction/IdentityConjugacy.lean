/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComplexConjugacy
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-! # Actual derived adjunctions and identity comparisons -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory
open CategoryTheory.Functor
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Original identity comparisons are conjugate on bounded-below complexes. -/
theorem Adjunction.mapCochainComplexPlus_conjugate_id
    {L R : A ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R)
    (eL : L ≅ 𝟭 A) (eR : R ≅ 𝟭 A)
    (h : conjugateEquiv Adjunction.id adj eL.hom = eR.inv) :
    conjugateEquiv Adjunction.id adj.mapCochainComplexPlus
        (NatIso.mapCochainComplexPlus eL ≪≫ mapCochainComplexPlusIdIso A).hom =
      (NatIso.mapCochainComplexPlus eR ≪≫ mapCochainComplexPlusIdIso A).inv := by
  apply Adjunction.conjugateEquiv_eq_of_unit
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  apply ObjectProperty.hom_ext
  ext n
  change (𝟙 _) ≫ (𝟙 _ ≫ eR.inv.app (K.obj.X n)) =
    adj.unit.app (K.obj.X n) ≫ R.map (eL.hom.app (K.obj.X n) ≫ 𝟙 _)
  have hu := unit_conjugateEquiv Adjunction.id adj eL.hom (K.obj.X n)
  rw [h] at hu
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
    Category.id_comp, Category.comp_id] using hu

variable [HasDerivedCategory.{w} A] [EnoughInjectives A]

/-- The transported identity comparison retains the original right-derived unit. -/
theorem Functor.rightDerivedFunctorPlusIso_id_unit
    (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A) (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app K) := by
  have h := F.rightDerivedFunctorPlusIso_hom_app e K
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, h, Category.assoc, rightDerivedFunctorPlusIdIso_unit,
    ← Functor.map_comp]
  rfl

/-- The exact identity comparison square uses the original termwise identity. -/
theorem Functor.rightDerivedFunctorPlusIso_id_exactComparison
    (F : A ⥤ A) [F.Additive] [F.PreservesHomology]
    (e : F ≅ 𝟭 A) (K : CochainComplex.Plus A) :
    (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
        (DerivedCategory.Plus.Q.obj K) =
      F.rightDerivedFunctorPlusExactComparison.hom.app K ≫
        DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app K) := by
  apply (cancel_epi (F.rightDerivedFunctorPlusExactComparison.inv.app K)).mp
  rw [Functor.rightDerivedFunctorPlusExactComparison_inv_app,
    F.rightDerivedFunctorPlusIso_id_unit]
  rw [← Category.assoc]
  change _ = (F.rightDerivedFunctorPlusExactComparison.inv.app K ≫
    F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫ _
  rw [Iso.inv_hom_id_app, Category.id_comp]

/-- The inverse identity comparison square retains the original right-derived unit. -/
theorem Functor.rightDerivedFunctorPlusIso_id_originalUnit
    (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A) (K : CochainComplex.Plus A) :
    (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).inv.app
        (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).inv.app K) ≫
        F.rightDerivedFunctorPlusUnit.app K := by
  apply (cancel_mono
    ((F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
      (DerivedCategory.Plus.Q.obj K))).mp
  rw [Iso.inv_hom_id_app, Category.assoc, F.rightDerivedFunctorPlusIso_id_unit,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rfl

/-- Original conjugate identity comparisons remain conjugate for the actual derived adjunction. -/
theorem Adjunction.rightDerivedFunctorPlus_conjugate_id
    {L R : A ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology] (adj : L ⊣ R)
    (eL : L ≅ 𝟭 A) (eR : R ≅ 𝟭 A)
    (h : conjugateEquiv Adjunction.id adj eL.hom = eR.inv) :
    conjugateEquiv Adjunction.id adj.rightDerivedFunctorPlus
        (L.rightDerivedFunctorPlusIso eL ≪≫ rightDerivedFunctorPlusIdIso A).hom =
      (R.rightDerivedFunctorPlusIso eR ≪≫ rightDerivedFunctorPlusIdIso A).inv := by
  let Q : CochainComplex.Plus A ⥤ DerivedCategory.Plus A := DerivedCategory.Plus.Q
  let c : Q ⋙ 𝟭 _ ≅ 𝟭 _ ⋙ Q := rightUnitor Q ≪≫ (leftUnitor Q).symm
  refine Adjunction.conjugateEquiv_eq_of_localization Q Q (CochainComplex.Plus.quasiIso A)
    Adjunction.id adj.mapCochainComplexPlus Adjunction.id adj.rightDerivedFunctorPlus
    c L.rightDerivedFunctorPlusExactComparison c.inv R.rightDerivedFunctorPlusUnit
    _ _ _ _ (adj.mapCochainComplexPlus_conjugate_id eL eR h) ?_ ?_ ?_ ?_
  · intro K
    simp only [c, Q, Functor.id_obj, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, rightUnitor_hom_app, rightUnitor_inv_app,
      leftUnitor_hom_app, leftUnitor_inv_app, Adjunction.id_unit,
      NatTrans.id_app, Functor.id_map, Functor.map_id, Category.id_comp]
  · exact adj.rightDerivedFunctorPlus_unit_fac
  · intro K
    simpa only [c, Q, Functor.id_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      rightUnitor_hom_app, leftUnitor_inv_app, Category.comp_id]
      using L.rightDerivedFunctorPlusIso_id_exactComparison eL K
  · intro K
    simpa only [c, Q, Functor.comp_obj, Functor.id_obj, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app,
      rightUnitor_inv_app, leftUnitor_hom_app, Category.id_comp]
      using R.rightDerivedFunctorPlusIso_id_originalUnit eR K

end CategoryTheory
