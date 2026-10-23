/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Complex
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactComparison

/-!
# Exact comparison for a canonical derived square

The two original composition isomorphisms and the intervening original functor
isomorphism determine both squares. Their compatibility follows from the original
units of exact functors. No direct-image derived unit is cancelled.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D) (M N : A ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive] [M.Additive] [N.Additive]
  (eA : M ≅ G ⋙ V) (eB : N ≅ F ⋙ H) (t : M ≅ N)

omit [HasDerivedCategory A] [EnoughInjectives A] [HasDerivedCategory B]
  [EnoughInjectives B] [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
private theorem mapCochainComplexPlus_square_app (Z : CochainComplex.Plus A) :
    ((TwoSquare.mk _ _ _ _ (eA.symm ≪≫ t ≪≫ eB).hom).mapCochainComplexPlus).app Z =
      (NatIso.mapCochainComplexPlus eA ≪≫ mapCochainComplexPlusCompIso G V).inv.app Z ≫
        (NatIso.mapCochainComplexPlus t).hom.app Z ≫
        (NatIso.mapCochainComplexPlus eB ≪≫ mapCochainComplexPlusCompIso F H).hom.app Z := by
  apply ObjectProperty.hom_ext
  ext n
  change (𝟙 _ ≫ (eA.inv.app (Z.obj.X n) ≫ t.hom.app (Z.obj.X n) ≫
      eB.hom.app (Z.obj.X n)) ≫ 𝟙 _) =
    (𝟙 _ ≫ eA.inv.app (Z.obj.X n)) ≫ t.hom.app (Z.obj.X n) ≫
      (eB.hom.app (Z.obj.X n) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

variable [F.PreservesHomology] [H.PreservesHomology] [G.PreservesHomology]
  [V.PreservesHomology] [M.PreservesHomology] [N.PreservesHomology]

/-- The literal exact-comparison square, retained as a shared formula for specialization. -/
def ExactComparisonSquareEquation
    (α : TwoSquare G F V H)
    (αD : TwoSquare G.rightDerivedFunctorPlus F.rightDerivedFunctorPlus
      V.rightDerivedFunctorPlus H.rightDerivedFunctorPlus) (Z : CochainComplex.Plus A) : Prop :=
  V.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      V.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z) ≫
      DerivedCategory.Plus.Q.map (α.mapCochainComplexPlus.app Z) =
    αD.app (DerivedCategory.Plus.Q.obj Z) ≫
      H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj Z)

/-- The native derived square of exact functors respects the original exact comparisons. -/
theorem rightDerivedFunctorPlus_exactSquare (Z : CochainComplex.Plus A) :
    let a := M.rightDerivedFunctorPlusIso eA ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology G V
    let b := N.rightDerivedFunctorPlusIso eB ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F H
    (V.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        V.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z)) ≫
      DerivedCategory.Plus.Q.map
        (((TwoSquare.mk _ _ _ _ (eA.symm ≪≫ t ≪≫ eB).hom).mapCochainComplexPlus).app Z) =
      (a.symm ≪≫ M.rightDerivedFunctorPlusIso t ≪≫ b).hom.app
          (DerivedCategory.Plus.Q.obj Z) ≫
        (H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          H.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj Z)) := by
  let a := M.rightDerivedFunctorPlusIso eA ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology G V
  let b := N.rightDerivedFunctorPlusIso eB ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology F H
  let d := M.rightDerivedFunctorPlusIso t
  let aC := NatIso.mapCochainComplexPlus eA ≪≫ mapCochainComplexPlusCompIso G V
  let bC := NatIso.mapCochainComplexPlus eB ≪≫ mapCochainComplexPlusCompIso F H
  let tC := NatIso.mapCochainComplexPlus t
  let EA := V.rightDerivedFunctorPlus.map
    (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      V.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z)
  let EB := H.rightDerivedFunctorPlus.map
    (F.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj Z)
  let α := (TwoSquare.mk _ _ _ _ (eA.symm ≪≫ t ≪≫ eB).hom).mapCochainComplexPlus
  have hA : a.hom.app (DerivedCategory.Plus.Q.obj Z) ≫ EA =
      M.rightDerivedFunctorPlusExactComparison.hom.app Z ≫
        DerivedCategory.Plus.Q.map (aC.hom.app Z) :=
    rightDerivedFunctorPlusCompIso_exactComparison_square G V M eA Z
  have hB : b.hom.app (DerivedCategory.Plus.Q.obj Z) ≫ EB =
      N.rightDerivedFunctorPlusExactComparison.hom.app Z ≫
        DerivedCategory.Plus.Q.map (bC.hom.app Z) :=
    rightDerivedFunctorPlusCompIso_exactComparison_square F H N eB Z
  have hT := rightDerivedFunctorPlusIso_exactComparison M N t Z
  change d.hom.app (DerivedCategory.Plus.Q.obj Z) ≫
      N.rightDerivedFunctorPlusExactComparison.hom.app Z =
    M.rightDerivedFunctorPlusExactComparison.hom.app Z ≫
      DerivedCategory.Plus.Q.map (tC.hom.app Z) at hT
  have hα : α.app Z = aC.inv.app Z ≫ tC.hom.app Z ≫ bC.hom.app Z :=
    mapCochainComplexPlus_square_app F H G V M N eA eB t Z
  have hc : DerivedCategory.Plus.Q.map (aC.hom.app Z) ≫
      DerivedCategory.Plus.Q.map (aC.inv.app Z) = 𝟙 _ := by
    rw [← Functor.map_comp, aC.hom_inv_id_app, Functor.map_id]
  change EA ≫ DerivedCategory.Plus.Q.map (α.app Z) =
    (a.symm ≪≫ d ≪≫ b).hom.app (DerivedCategory.Plus.Q.obj Z) ≫ EB
  apply (cancel_epi (a.hom.app (DerivedCategory.Plus.Q.obj Z))).mp
  rw [← Category.assoc, hA, hα]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hc]
  rw [← Category.assoc, ← hT, Category.assoc, ← hB]

/-- The canonical exact square satisfies the shared literal comparison formula. -/
theorem exactComparisonSquareEquation (Z : CochainComplex.Plus A) :
    ExactComparisonSquareEquation F H G V
      (TwoSquare.mk _ _ _ _ (eA.symm ≪≫ t ≪≫ eB).hom)
      (TwoSquare.mk _ _ _ _
        ((M.rightDerivedFunctorPlusIso eA ≪≫
            rightDerivedFunctorPlusCompIsoOfPreservesHomology G V).symm ≪≫
          M.rightDerivedFunctorPlusIso t ≪≫
          (N.rightDerivedFunctorPlusIso eB ≪≫
            rightDerivedFunctorPlusCompIsoOfPreservesHomology F H)).hom) Z := by
  have h := rightDerivedFunctorPlus_exactSquare F H G V M N eA eB t Z
  simpa only [ExactComparisonSquareEquation, Category.assoc] using h

end CategoryTheory
