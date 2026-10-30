/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Pullback.Coefficients
public import Aglib.CategoryTheory.Functor.Flat
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Actual flat abelian Kan extensions and original coefficient units

The coefficient world bounds the actual comma-colimit sizes. The two site
object/Hom worlds remain distinct. Forgetting preserves those filtered
colimits, then reflects the actual universal property through the original
Kan desc map. The inverse coefficient comparison retains the original unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe c₁ h₁ c₂ h₂ w

/-- Forgetting addition preserves the original flat left Kan extension at
the actual comma-colimit bounds, without identifying the two site worlds. -/
theorem forget_preserves_flat_leftKan
    {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
    (F : C ⥤ D) [RepresentablyFlat F]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max c₁ h₁ h₂ w}) :
    (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}).PreservesLeftKanExtension
      P F.op := by
  have (T : Dᵒᵖ) : IsFiltered (CostructuredArrow F.op T) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F T.unop)
  have : PreservesFilteredColimitsOfSize.{h₁, max c₁ h₂}
      (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}) :=
    preservesFilteredColimitsOfSize_shrink.{max c₁ h₂, max c₁ h₁ h₂ w,
      h₁, max c₁ h₁ h₂ w}
      (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w})
  have (T : Dᵒᵖ) : PreservesColimitsOfShape (CostructuredArrow F.op T)
      (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}) := inferInstance
  have (T : Dᵒᵖ) :
      (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}).PreservesPointwiseLeftKanExtensionAt
        P F.op T := inferInstance
  infer_instance

/-- Reflect the universal property of the same original abelian target,
using the original chosen desc map and conservative forgetting. -/
theorem abelian_isLeftKan_of_underlying
    {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
    (F : C ⥤ D) [RepresentablyFlat F]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max c₁ h₁ h₂ w})
    (Q : Dᵒᵖ ⥤ AddCommGrpCat.{max c₁ h₁ h₂ w}) (α : P ⟶ F.op ⋙ Q)
    (h : (Q ⋙ CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}).IsLeftKanExtension
      (Functor.whiskerRight α (CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}) ≫
        (Functor.associator _ _ _).hom)) : Q.IsLeftKanExtension α := by
  let G := CategoryTheory.forget AddCommGrpCat.{max c₁ h₁ h₂ w}
  let E := F.op.leftKanExtension P
  let unitMap := F.op.leftKanExtensionUnit P
  let β : E ⟶ Q := E.descOfIsLeftKanExtension unitMap Q α
  have := forget_preserves_flat_leftKan.{c₁, h₁, c₂, h₂, w} F P
  let := h
  have hβ : IsIso (Functor.whiskerRight β G) := by
    apply (Functor.isLeftKanExtension_iff_isIso (Functor.whiskerRight β G)
      (Functor.whiskerRight unitMap G ≫ (Functor.associator _ _ _).hom)
      (Functor.whiskerRight α G ≫ (Functor.associator _ _ _).hom) ?_).mp
    · exact h
    · apply NatTrans.ext
      funext U
      change G.map (unitMap.app U) ≫ G.map (β.app (F.op.obj U)) = G.map (α.app U)
      rw [← G.map_comp]
      exact congrArg G.map (E.descOfIsLeftKanExtension_fac_app unitMap Q α U)
  have : IsIso (((Functor.whiskeringRight _ _ _).obj G).map β) := hβ
  have : IsIso β := isIso_of_reflects_iso β ((Functor.whiskeringRight _ _ _).obj G)
  exact (Functor.isLeftKanExtension_iff_isIso β unitMap α
    (E.descOfIsLeftKanExtension_fac unitMap Q α)).mpr inferInstance

section CoefficientInverse

universe a₁ b₁ a₂ b₂

variable {C : Type c₁} [Category.{h₁} C] {D : Type c₂} [Category.{h₂} D]
  {A : Type a₁} [Category.{b₁} A] {B : Type a₂} [Category.{b₂} B]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] (U : A ⥤ B)
  [J.HasSheafCompose U] [K.HasSheafCompose U]
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ B, G.op.HasLeftKanExtension P]
  [U.PreservesLeftKanExtensions G.op] [K.PreservesSheafification U]

/-- The original four factors, retaining the chosen pullbacks and coefficient comparison. -/
def sheafPullbackCoefficientInverseIso :
    G.sheafPullback A J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ G.sheafPullback B J K :=
      Functor.isoWhiskerRight (sheafPullbackConstruction.sheafPullbackIso G A J K)
          (sheafCompose K U) ≪≫
        Functor.isoWhiskerLeft (sheafToPresheaf J A ⋙ G.op.lan)
          (sheafComposeNatIso K U (sheafificationAdjunction K A)
            (sheafificationAdjunction K B)).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (sheafToPresheaf J A) (U.lanCompIsoOfPreserves G.op))
          (presheafToSheaf K B) ≪≫
        Functor.isoWhiskerLeft (sheafCompose J U)
          (sheafPullbackConstruction.sheafPullbackIso G B J K).symm

/-- These original four factors equal the inverse of the existing coefficient comparison. -/
theorem sheafPullbackCoefficientInverseIso_eq_symm :
    sheafPullbackCoefficientInverseIso G J K U =
      (sheafPullbackCoefficientIso G J K U).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  dsimp only [sheafPullbackCoefficientInverseIso, sheafPullbackCoefficientIso,
    sheafPullbackConstructionCoefficientIso, Iso.trans, Iso.symm, isoWhiskerLeft,
    isoWhiskerRight, Functor.mapIso, whiskeringLeft, whiskeringRight,
    whiskerLeft, whiskerRight, Functor.associator, Functor.category, NatTrans.vcomp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  let sourceObj : B := U.obj (((G.sheafPullback A J K).obj P).obj.obj V)
  let firstObj : B :=
    U.obj (((presheafToSheaf K A).obj (G.op.lan.obj P.obj)).obj.obj V)
  let secondObj : B :=
    ((presheafToSheaf K B).obj (G.op.lan.obj P.obj ⋙ U)).obj.obj V
  let thirdObj : B :=
    ((presheafToSheaf K B).obj (G.op.lan.obj (P.obj ⋙ U))).obj.obj V
  let targetObj : B :=
    ((G.sheafPullback B J K).obj ((sheafCompose J U).obj P)).obj.obj V
  let firstMap : sourceObj ⟶ firstObj :=
    U.map (((sheafPullbackConstruction.sheafPullbackIso G A J K).hom.app P).hom.app V)
  let secondMap : firstObj ⟶ secondObj :=
    ((sheafComposeNatIso K U (sheafificationAdjunction K A)
      (sheafificationAdjunction K B)).inv.app (G.op.lan.obj P.obj)).hom.app V
  let thirdMap : secondObj ⟶ thirdObj :=
    ((presheafToSheaf K B).map ((U.lanCompIsoOfPreserves G.op).hom.app P.obj)).hom.app V
  let lastMap : thirdObj ⟶ targetObj :=
    ((sheafPullbackConstruction.sheafPullbackIso G B J K).inv.app
      ((sheafCompose J U).obj P)).hom.app V
  change firstMap ≫ secondMap ≫ thirdMap ≫ lastMap =
    (firstMap ≫ ((secondMap ≫ 𝟙 secondObj) ≫ thirdMap)) ≫ lastMap
  simp only [Category.comp_id, Category.assoc]

/-- The old inverse orientation preserves the same actual chosen unit. -/
theorem sheafPullbackCoefficientIso_inv_unit (P : Sheaf J A) :
    (sheafCompose J U).map ((G.sheafAdjunctionContinuous A J K).unit.app P) ≫
      (G.sheafPushforwardContinuous B J K).map
        ((sheafPullbackCoefficientIso G J K U).inv.app P) =
      (G.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J U).obj P) := by
  let R := G.sheafPushforwardContinuous B J K
  let e := sheafPullbackCoefficientIso G J K U
  let T : Sheaf K B := (sheafCompose J U ⋙ G.sheafPullback B J K).obj P
  let η : (sheafCompose J U).obj P ⟶ R.obj T :=
    (G.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J U).obj P)
  calc
    _ = (η ≫ R.map (e.hom.app P)) ≫ R.map (e.inv.app P) :=
      congrArg (fun f => f ≫ R.map (e.inv.app P))
        (sheafPullbackCoefficientIso_unit G J K U P).symm
    _ = η ≫ R.map (𝟙 T) := by
      rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    _ = η ≫ 𝟙 _ := congrArg (fun f => η ≫ f) (R.map_id T)
    _ = η := Category.comp_id η

/-- The original four-factor comparison preserves the actual original unit. -/
theorem sheafPullbackCoefficientInverseIso_unit (P : Sheaf J A) :
    (sheafCompose J U).map ((G.sheafAdjunctionContinuous A J K).unit.app P) ≫
      (G.sheafPushforwardContinuous B J K).map
        ((sheafPullbackCoefficientInverseIso G J K U).hom.app P) =
      (G.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J U).obj P) := by
  rw [sheafPullbackCoefficientInverseIso_eq_symm]
  exact sheafPullbackCoefficientIso_inv_unit G J K U P

end CoefficientInverse

end CategoryTheory.Functor
