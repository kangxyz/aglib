/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Detecting the actual inverse-image unit through a left Kan extension

For a continuous functor of sites, the constructed inverse image is the left
Kan extension followed by sheafification. Its unit is the composite of those
two original units. A represented comparison identifies the Kan extension with
an actual sheaf, so monicity or invertibility of its original section map
passes to the unit of the given inverse-image adjunction. The comparison uses
the native uniqueness of left adjoints to the same continuous pushforward.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (G : C ⥤ D) (A : Type uA) [Category.{vA} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension P] [HasWeakSheafify K A]

/-- The constructed inverse-image unit is the original Kan unit followed by
the original sheafification unit, on underlying presheaves. -/
theorem sheafPullbackConstruction.unit_app_hom (P : Sheaf J A) :
    ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P).hom =
      G.op.leftKanExtensionUnit P.obj ≫
        Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (iC := sheafToPresheaf J A) (iD := 𝟭 (Sheaf K A))
    (L := sheafPullbackConstruction.sheafPullback G A J K)
    (R := G.sheafPushforwardContinuous A J K)
    ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _) P
  change (sheafToPresheaf J A).map
    ((sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app P) = _
  refine h.trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Adjunction.comp_unit_app,
    Functor.lanAdjunction_unit]
  apply NatTrans.ext
  funext U
  change (((G.op.leftKanExtensionUnit P.obj).app U ≫
      (toSheafify K (G.op.lan.obj P.obj)).app (G.op.obj U)) ≫ 𝟙 _ ≫ 𝟙 _) =
    (G.op.leftKanExtensionUnit P.obj).app U ≫
      (toSheafify K (G.op.lan.obj P.obj)).app (G.op.obj U)
  simp only [Category.comp_id]

variable {L : Sheaf J A ⥤ Sheaf K A}
  (adj : L ⊣ G.sheafPushforwardContinuous A J K)

/-- A monic original Kan section map gives a monic unit for the actual given
inverse-image adjunction. The Kan target is identified with the given sheaf. -/
theorem mono_unit_of_leftKanIso (P : Sheaf J A) (Q : Sheaf K A)
    (e : G.op.lan.obj P.obj ≅ Q.obj) (α : P.obj ⟶ G.op ⋙ Q.obj)
    (h : G.op.leftKanExtensionUnit P.obj ≫ Functor.whiskerLeft G.op e.hom = α)
    [Mono α] : Mono (adj.unit.app P) := by
  let monoKan : Mono (G.op.leftKanExtensionUnit P.obj) := mono_of_mono_fac h
  have hsheaf : Presheaf.IsSheaf K (G.op.lan.obj P.obj) :=
    (Presheaf.isSheaf_of_iso_iff e).mpr Q.property
  let isoSheaf : IsIso (toSheafify K (G.op.lan.obj P.obj)) := isIso_toSheafify K hsheaf
  let isoWhisker : IsIso (Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) :=
    (Functor.isoWhiskerLeft G.op (asIso (toSheafify K (G.op.lan.obj P.obj)))).isIso_hom
  let monoWhisker : Mono (Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) :=
    @IsIso.mono_of_iso _ _ _ _ _ isoWhisker
  have hComposite : Mono (G.op.leftKanExtensionUnit P.obj ≫
      Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) :=
    mono_comp' monoKan monoWhisker
  let constructed := sheafPullbackConstruction.sheafAdjunctionContinuous G A J K
  let monoConstructed : Mono (constructed.unit.app P) := by
    apply (sheafToPresheaf J A).mono_of_mono_map
    change Mono (constructed.unit.app P).hom
    exact (sheafPullbackConstruction.unit_app_hom G A J K P).symm ▸ hComposite
  let c := adj.leftAdjointUniq constructed
  have hc : adj.unit.app P ≫
      (G.sheafPushforwardContinuous A J K).map (c.app P).hom = constructed.unit.app P :=
    Adjunction.unit_leftAdjointUniq_hom_app adj constructed P
  exact mono_of_mono_fac hc

/-- Invertible Kan and sheafification units give an invertible unit for the
actual given inverse-image adjunction. -/
theorem isIso_unit_of_leftKanUnit (P : Sheaf J A)
    [IsIso (G.op.leftKanExtensionUnit P.obj)]
    [IsIso (toSheafify K (G.op.lan.obj P.obj))] : IsIso (adj.unit.app P) := by
  let isoWhisker : IsIso (Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) :=
    (Functor.isoWhiskerLeft G.op (asIso (toSheafify K (G.op.lan.obj P.obj)))).isIso_hom
  have hComposite : IsIso (G.op.leftKanExtensionUnit P.obj ≫
      Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj P.obj))) :=
    IsIso.comp_isIso' inferInstance isoWhisker
  let constructed := sheafPullbackConstruction.sheafAdjunctionContinuous G A J K
  let isoConstructed : IsIso (constructed.unit.app P) := by
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf J A)).mp
    change IsIso (constructed.unit.app P).hom
    exact (sheafPullbackConstruction.unit_app_hom G A J K P).symm ▸ hComposite
  let c := adj.leftAdjointUniq constructed
  have hc : adj.unit.app P ≫
      (G.sheafPushforwardContinuous A J K).map (c.app P).hom = constructed.unit.app P :=
    Adjunction.unit_leftAdjointUniq_hom_app adj constructed P
  let isoActualComposite : IsIso (adj.unit.app P ≫
      (G.sheafPushforwardContinuous A J K).map (c.app P).hom) := hc.symm ▸ isoConstructed
  exact IsIso.of_isIso_comp_right (adj.unit.app P)
    ((G.sheafPushforwardContinuous A J K).map (c.app P).hom)

/-- An invertible original Kan section map gives an invertible unit for the
actual given inverse-image adjunction, through the same represented target. -/
theorem isIso_unit_of_leftKanIso (P : Sheaf J A) (Q : Sheaf K A)
    (e : G.op.lan.obj P.obj ≅ Q.obj) (α : P.obj ⟶ G.op ⋙ Q.obj)
    (h : G.op.leftKanExtensionUnit P.obj ≫ Functor.whiskerLeft G.op e.hom = α)
    [IsIso α] : IsIso (adj.unit.app P) := by
  let isoComposite : IsIso (G.op.leftKanExtensionUnit P.obj ≫ Functor.whiskerLeft G.op e.hom) :=
    h.symm ▸ inferInstance
  let isoWhisker : IsIso (Functor.whiskerLeft G.op e.hom) :=
    (Functor.isoWhiskerLeft G.op e).isIso_hom
  let isoKan : IsIso (G.op.leftKanExtensionUnit P.obj) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (G.op.leftKanExtensionUnit P.obj)
      (Functor.whiskerLeft G.op e.hom) isoWhisker isoComposite
  have hsheaf : Presheaf.IsSheaf K (G.op.lan.obj P.obj) :=
    (Presheaf.isSheaf_of_iso_iff e).mpr Q.property
  let isoSheaf : IsIso (toSheafify K (G.op.lan.obj P.obj)) := isIso_toSheafify K hsheaf
  exact isIso_unit_of_leftKanUnit G A J K adj P

end CategoryTheory.Functor
