/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Associativity of the installed bounded-below composition comparison -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C] {D : Type u₄} [Category.{v₄} D] [Abelian D]
  [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]

/-- On an original localized complex, both parenthesizations of the exact-second-factor
composition comparison retain the same three original units. -/
-- Retain the middle-functor hypothesis shared by the two associativity branches.
@[nolint unusedArguments]
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc_app
    [G.PreservesHomology] [H.PreservesHomology] [(G ⋙ H).PreservesHomology]
    (K : CochainComplex.Plus A) :
    (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology F (G ⋙ H)).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology G H).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
      H.rightDerivedFunctorPlusUnit.app
          (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
  calc
    _ = (G ⋙ H).rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        ((rightDerivedFunctorPlusCompIsoOfPreservesHomology G H).hom.app
          (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
          (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).map
            (F.rightDerivedFunctorPlusUnit.app K)) := by
      simpa only [Category.assoc, comp_obj] using congrArg
        (fun t => (G ⋙ H).rightDerivedFunctorPlusUnit.app
          (F.mapCochainComplexPlus.obj K) ≫ t)
        ((rightDerivedFunctorPlusCompIsoOfPreservesHomology G H).hom.naturality
          (F.rightDerivedFunctorPlusUnit.app K))
    _ = _ := by
      rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
      exact Category.assoc _ _ _

/-- On an original localized complex, the other parenthesization retains the same
three original units. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc_app'
    [G.PreservesHomology] [H.PreservesHomology] (K : CochainComplex.Plus A) :
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology (F ⋙ G) H).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        H.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
            (DerivedCategory.Plus.Q.obj K)) =
      H.rightDerivedFunctorPlusUnit.app
          (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    Category.assoc, ← H.rightDerivedFunctorPlus.map_comp,
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    H.rightDerivedFunctorPlus.map_comp]
  rfl

/-- On an original localized complex, both parenthesizations of the
injective-preserving-first-factor
composition comparison retain the same three original units. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc_app
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] (K : CochainComplex.Plus A) :
    (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F (G ⋙ H)).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
      H.rightDerivedFunctorPlusUnit.app
          (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]
  calc
    _ = (G ⋙ H).rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H).hom.app
          (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
          (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).map
            (F.rightDerivedFunctorPlusUnit.app K)) := by
      simpa only [Category.assoc, comp_obj] using congrArg
        (fun t => (G ⋙ H).rightDerivedFunctorPlusUnit.app
          (F.mapCochainComplexPlus.obj K) ≫ t)
        ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H).hom.naturality
          (F.rightDerivedFunctorPlusUnit.app K))
    _ = _ := by
      rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]
      exact Category.assoc _ _ _

/-- On an original localized complex, the other parenthesization retains the same
three original units. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc_app'
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] (K : CochainComplex.Plus A) :
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfPreservesInjectives (F ⋙ G) H).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        H.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G).hom.app
            (DerivedCategory.Plus.Q.obj K)) =
      H.rightDerivedFunctorPlusUnit.app
          (G.mapCochainComplexPlus.obj (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
  rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
    Category.assoc, ← H.rightDerivedFunctorPlus.map_comp,
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
    H.rightDerivedFunctorPlus.map_comp]
  rfl

/-- Associativity of the native composition comparisons, with the actual derived
associator and no new choice of comparison. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc
    [G.PreservesHomology] [H.PreservesHomology] [(G ⋙ H).PreservesHomology] :
    rightDerivedFunctorPlusCompIsoOfPreservesHomology (F ⋙ G) H ≪≫
        isoWhiskerRight (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G)
          H.rightDerivedFunctorPlus ≪≫
        associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus H.rightDerivedFunctorPlus =
      ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusIso (associator F G H) ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F (G ⋙ H) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIsoOfPreservesHomology G H) := by
  apply Iso.ext
  apply ((F ⋙ G) ⋙ H).rightDerivedFunctorPlus.rightDerived_ext
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  have hm : (NatIso.mapCochainComplexPlus (associator F G H)).hom.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom,
    associator_hom_app, Category.comp_id, comp_obj]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, hm, map_id,
      Category.id_comp]
  exact (rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc_app' F G H K).trans
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc_app F G H K).symm

/-- Associativity of the native composition comparisons, with the actual derived
associator and no new choice of comparison. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] :
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives (F ⋙ G) H ≪≫
        isoWhiskerRight (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G)
          H.rightDerivedFunctorPlus ≪≫
        associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus H.rightDerivedFunctorPlus =
      ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusIso (associator F G H) ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F (G ⋙ H) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H) := by
  apply Iso.ext
  apply ((F ⋙ G) ⋙ H).rightDerivedFunctorPlus.rightDerived_ext
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  have hm : (NatIso.mapCochainComplexPlus (associator F G H)).hom.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom,
    associator_hom_app, Category.comp_id, comp_obj]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, hm, map_id,
      Category.id_comp]
  exact (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc_app' F G H K).trans
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc_app F G H K).symm

end CategoryTheory.Functor
