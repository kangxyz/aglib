/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Coefficients and pullback on arbitrary sites

A coefficient functor that preserves the relevant left Kan extensions and
sheafification commutes with the original continuous-site pullback. The
comparison uses the native Kan extension and sheafification comparisons.
The hypotheses refer to these constructions, not to blanket exactness of the
coefficient functor. Constant-ring étale module pullback is the first consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] (U : A ⥤ B)
  [J.HasSheafCompose U] [K.HasSheafCompose U]
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ B, G.op.HasLeftKanExtension P]
  [U.PreservesLeftKanExtensions G.op] [K.PreservesSheafification U]

/-- The original Kan-extension/sheafification comparison for a single input sheaf. -/
def sheafPullbackConstructionCoefficientComponent (P : Sheaf J A) :
    (sheafPullbackConstruction.sheafPullback G B J K).obj ((sheafCompose J U).obj P) ≅
      (sheafCompose K U).obj ((sheafPullbackConstruction.sheafPullback G A J K).obj P) :=
  (presheafToSheaf K B).mapIso
    (U.leftKanExtensionCompIsoOfPreserves P.obj G.op).symm ≪≫
      (sheafComposeNatIso K U (sheafificationAdjunction K A)
        (sheafificationAdjunction K B)).app (G.op.lan.obj P.obj)

/-- Coefficients commute with the native Kan-extension construction of sheaf pullback. -/
def sheafPullbackConstructionCoefficientIso :
    sheafCompose J U ⋙ sheafPullbackConstruction.sheafPullback G B J K ≅
      sheafPullbackConstruction.sheafPullback G A J K ⋙ sheafCompose K U :=
  isoWhiskerLeft (sheafToPresheaf J A)
    (isoWhiskerRight (U.lanCompIsoOfPreserves G.op).symm (presheafToSheaf K B) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft G.op.lan
        (sheafComposeNatIso K U (sheafificationAdjunction K A)
          (sheafificationAdjunction K B)))

/-- Coefficient comparison for the original chosen continuous-site pullback functors. -/
def sheafPullbackCoefficientIso :
    sheafCompose J U ⋙ G.sheafPullback B J K ≅
      G.sheafPullback A J K ⋙ sheafCompose K U :=
  isoWhiskerLeft (sheafCompose J U) (sheafPullbackConstruction.sheafPullbackIso G B J K) ≪≫
    sheafPullbackConstructionCoefficientIso G J K U ≪≫
      isoWhiskerRight (sheafPullbackConstruction.sheafPullbackIso G A J K).symm
        (sheafCompose K U)

/-- The Kan-extension construction retains the actual sheafification and Kan units. -/
theorem sheafPullbackConstruction_unit_hom (P : Sheaf J A) :
    ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P).hom =
      G.op.leftKanExtensionUnit P.obj ≫
        whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj)) := by
  change (sheafToPresheaf J A).map
    ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P) = _
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _)
    (L := sheafPullbackConstruction.sheafPullback G A J K)
    (R := G.sheafPushforwardContinuous A J K) (Iso.refl _) (Iso.refl _) P
  exact h.trans (by
    simp only [Adjunction.comp_unit_app, lanAdjunction_unit, lanUnit,
      Iso.refl_hom, NatTrans.id_app]
    exact (congrArg (fun t =>
      (G.op.leftKanExtensionUnit P.obj ≫
        whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) ≫ t ≫ 𝟙 _)
      ((sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj G.op).map_id _)).trans
        ((congrArg (fun t =>
          (G.op.leftKanExtensionUnit P.obj ≫
            whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) ≫ t)
          (Category.id_comp (𝟙 _))).trans (Category.comp_id _)))

-- The preserved Kan extension and `lan` select definitionally equal colimit objects
-- through different proof instances; expose this native choice only in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient comparison for the construction preserves its original unit. -/
@[reassoc]
theorem sheafPullbackConstructionCoefficientIso_unit (P : Sheaf J A) :
    (sheafPullbackConstruction.sheafAdjunctionContinuous G B J K).unit.app
        ((sheafCompose J U).obj P) ≫
      (G.sheafPushforwardContinuous B J K).map
        ((sheafPullbackConstructionCoefficientIso G J K U).hom.app P) =
    (sheafCompose J U).map
      ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P) := by
  apply ObjectProperty.hom_ext
  change ((sheafPullbackConstruction.sheafAdjunctionContinuous G B J K).unit.app
      ((sheafCompose J U).obj P)).hom ≫
      whiskerLeft G.op ((sheafPullbackConstructionCoefficientIso G J K U).hom.app P).hom =
    whiskerRight ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P).hom U
  rw [sheafPullbackConstruction_unit_hom, sheafPullbackConstruction_unit_hom]
  simp only [sheafPullbackConstructionCoefficientIso, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp]
  ext V
  change ((G.op.leftKanExtensionUnit (P.obj ⋙ U)).app V ≫
      (toSheafify K (G.op.lan.obj (P.obj ⋙ U))).app (G.op.obj V)) ≫
        ((sheafifyMap K (U.leftKanExtensionCompIsoOfPreserves P.obj G.op).inv).app
          (G.op.obj V) ≫
        (sheafifyComposeIso K U (G.op.lan.obj P.obj)).hom.app (G.op.obj V)) =
      U.map ((G.op.leftKanExtensionUnit P.obj).app V ≫
        (toSheafify K (G.op.lan.obj P.obj)).app (G.op.obj V))
  simp only [Category.assoc]
  have hn := NatTrans.congr_app
    (toSheafify_naturality K (U.leftKanExtensionCompIsoOfPreserves P.obj G.op).inv)
    (G.op.obj V)
  have hs := NatTrans.congr_app
    (sheafComposeIso_hom_fac K U (G.op.lan.obj P.obj)) (G.op.obj V)
  dsimp only [NatTrans.comp_app, whiskerRight_app] at hn hs
  calc
    _ = (G.op.leftKanExtensionUnit (P.obj ⋙ U)).app V ≫
        (U.leftKanExtensionCompIsoOfPreserves P.obj G.op).inv.app (G.op.obj V) ≫
          (toSheafify K (G.op.lan.obj P.obj ⋙ U)).app (G.op.obj V) ≫
          (sheafifyComposeIso K U (G.op.lan.obj P.obj)).hom.app (G.op.obj V) := by
      rw [← Category.assoc (toSheafify K (G.op.lan.obj (P.obj ⋙ U)) |>.app
        (G.op.obj V))]
      erw [← hn]
      rw [Category.assoc]
      rfl
    _ = U.map ((G.op.leftKanExtensionUnit P.obj).app V) ≫
        U.map ((toSheafify K (G.op.lan.obj P.obj)).app (G.op.obj V)) := by
      rw [hs, ← Category.assoc, leftKanExtensionCompIsoOfPreserves_inv_fac_app]
    _ = _ := (U.map_comp _ _).symm

/-- The coefficient comparison preserves the original chosen pullback unit. -/
@[reassoc]
theorem sheafPullbackCoefficientIso_unit (P : Sheaf J A) :
    (G.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J U).obj P) ≫
      (G.sheafPushforwardContinuous B J K).map
        ((sheafPullbackCoefficientIso G J K U).hom.app P) =
    (sheafCompose J U).map ((G.sheafAdjunctionContinuous A J K).unit.app P) := by
  dsimp only [sheafPullbackCoefficientIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [show (G.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J U).obj P) ≫
      (G.sheafPushforwardContinuous B J K).map
        ((sheafPullbackConstruction.sheafPullbackIso G B J K).hom.app
          ((sheafCompose J U).obj P)) =
      (sheafPullbackConstruction.sheafAdjunctionContinuous G B J K).unit.app
        ((sheafCompose J U).obj P) from
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _]
  rw [sheafPullbackConstructionCoefficientIso_unit]
  change (sheafCompose J U).map
      ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P) ≫
      (sheafCompose J U).map ((G.sheafPushforwardContinuous A J K).map
        ((sheafPullbackConstruction.sheafPullbackIso G A J K).inv.app P)) = _
  rw [← Functor.map_comp]
  congr 1
  have h : (G.sheafAdjunctionContinuous A J K).unit.app P ≫
      (G.sheafPushforwardContinuous A J K).map
        ((sheafPullbackConstruction.sheafPullbackIso G A J K).hom.app P) =
      (sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ P
  rw [← h, Category.assoc, ← Functor.map_comp]
  simp only [Iso.hom_inv_id_app, Functor.map_id]
  exact Category.comp_id _

end CategoryTheory.Functor
