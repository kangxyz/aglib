/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Actual pullback of arbitrary-section nonvanishing opens

The pulled section is the original pullback-adjunction unit on the original
section. Its nonvanishing open is the literal inverse image. Open restriction
uses the native restriction module, its actual section comparison, and the
native isomorphism from restriction to pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing

variable {X Y : Scheme.{u}}

/-- The original adjunction unit applied to the actual global section. -/
def pullbackSection (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ s

/-- The native restriction section, through the actual restriction comparison. -/
def restrictSection (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ(M, ⊤)) : Γ(M.restrict f, ⊤) :=
  (M.restrictAppIso f ⊤).inv (M.presheaf.map (homOfLE le_top).op s)

/-- The actual restriction module is locally rank one through the canonical
restriction-to-pullback isomorphism. -/
def restrictLineBundle (f : X ⟶ Y) [IsOpenImmersion f] (L : LineBundle Y) : LineBundle X :=
  ⟨(Scheme.Modules.restrictFunctor f).obj L.val, isLocallyRankOne_of_iso X
    ((restrictFunctorIsoPullback f).app L.val).symm
    (pullbackLineBundle f L).property⟩

/-- The original global pullback section restricts to the unit on each
original inverse-image open. -/
theorem pullbackSection_restrict (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤))
    (U : Y.Opens) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE le_top).op
        (pullbackSection f M s) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U
        (M.presheaf.map (homOfLE le_top).op s) :=
  (PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction f).unit.app M).val
    (homOfLE (show U ≤ ⊤ from le_top)).op s).symm

/-- In a global actual unit frame, the pulled section has the literal
pullback of its original coefficient. -/
theorem pullbackSection_unitFrame (f : X ⟶ Y) (M : Y.Modules)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f).hom.val.app (op ⊤)
        (pullbackSection f M s) = f.appTop (e.hom.val.app (op ⊤) s) := by
  let A := pullbackPushforwardAdjunction f
  have hu := pullbackUnitIso_homEquiv f
  rw [Adjunction.homEquiv_unit] at hu
  have hn : e.hom ≫ A.unit.app (SheafOfModules.unit Y.ringCatSheaf) =
      A.unit.app M ≫ (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullback f).map e.hom) :=
    A.unit.naturality e.hom
  have h : A.unit.app M ≫ (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullback f).map e.hom ≫ (pullbackUnitIso f).hom) =
      e.hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    calc
      _ = (A.unit.app M ≫ (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullback f).map e.hom)) ≫
          (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom := by
        rw [Functor.map_comp, Category.assoc]
      _ = (e.hom ≫ A.unit.app (SheafOfModules.unit Y.ringCatSheaf)) ≫
          (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom :=
        congrArg (fun k => k ≫ (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom)
          hn.symm
      _ = _ := by rw [Category.assoc, hu]
  exact congrArg (fun k => k.val.app (op ⊤) s) h

/-- The image of an open of a chart lies in the original chart. -/
theorem image_le (U : X.Opens) (V : U.toScheme.Opens) : U.ι ''ᵁ V ≤ U := by
  simpa using U.ι.image_le_opensRange V

/-- Transport an original over-site frame to the actual restriction module. -/
def frameOnRestriction (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((overFunctorEquiv U).app M).symm ≪≫ (overEquiv U).functor.mapIso e ≪≫ overUnitIso U

/-- Recover an over-site frame from the actual restriction frame. -/
def frameFromRestriction (M : X.Modules) (U : X.Opens)
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app M ≪≫ d ≪≫ (overUnitIso U).symm)

theorem frameOnRestriction_from (M : X.Modules) (U : X.Opens)
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    frameOnRestriction M U (frameFromRestriction M U d) = d := by
  apply Iso.ext
  simp [frameOnRestriction, frameFromRestriction, Functor.preimageIso, Category.assoc]

/-- The restriction frame retains the original coefficient, through the
actual ring and module restriction comparisons. -/
theorem frameOnRestriction_coefficient (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : U.toScheme.Opens) (s : Γ(M, U.ι ''ᵁ V)) :
    (frameOnRestriction M U e).hom.val.app (op V) ((M.restrictAppIso U.ι V).inv s) =
      (U.ι.appIso V).hom
        (chartSectionEquiv X M U e (U.ι ''ᵁ V) (image_le U V) s) := by
  rfl

/-- A global frame on the actual restriction computes the original
nonvanishing open on that chart. -/
theorem image_basicOpen_restrictionFrame (L : LineBundle X) (s : Γ(L.val, ⊤))
    (U : X.Opens)
    (d : (Scheme.Modules.restrictFunctor U.ι).obj L.val ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    U.ι ''ᵁ U.toScheme.basicOpen
        (d.hom.val.app (op ⊤) (restrictSection U.ι L.val s)) =
      U ⊓ nonvanishingOpen L s := by
  let M : X.Modules := L.val
  let e := frameFromRestriction M U d
  let P := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  have he : frameOnRestriction M U e = d := frameOnRestriction_from M U d
  have hc := frameOnRestriction_coefficient M U e ⊤
    (M.presheaf.map (homOfLE (show P ≤ ⊤ from le_top)).op s)
  rw [he] at hc
  have hd : (U.ι.appIso ⊤).inv (d.hom.val.app (op ⊤) (restrictSection U.ι M s)) =
      chartSectionEquiv X M U e P (image_le U ⊤)
        (M.presheaf.map (homOfLE le_top).op s) := by
    rw [show d.hom.val.app (op ⊤) (restrictSection U.ι M s) =
      (U.ι.appIso ⊤).hom (chartSectionEquiv X M U e P (image_le U ⊤)
        (M.presheaf.map (homOfLE le_top).op s)) from hc]
    exact (U.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm_apply_apply _
  rw [Scheme.image_basicOpen, hd]
  have hs : M.val.map (homOfLE (image_le U ⊤)).op
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      M.val.map (homOfLE (show P ≤ ⊤ from le_top)).op s := by
    change (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      M.presheaf.map (homOfLE (image_le U ⊤)).op) s =
        M.presheaf.map (homOfLE (show P ≤ ⊤ from le_top)).op s
    rw [← Functor.map_comp]
    rfl
  have hres := Nonvanishing.basicOpen_coefficient_restrict M U e (image_le U ⊤)
    le_rfl (M.val.map (homOfLE le_top).op s)
  rw [hs] at hres
  calc
    _ = P ⊓ X.basicOpen (chartSectionEquiv X M U e U le_rfl
        (M.val.map (homOfLE le_top).op s)) := hres
    _ = X.basicOpen (chartSectionEquiv X M U e U le_rfl
        (M.val.map (homOfLE le_top).op s)) := by
      rw [show P = U by simp [P], inf_eq_right.mpr (X.basicOpen_le _)]
    _ = U ⊓ nonvanishingOpen L s := (inter_nonvanishingOpen L s U e).symm

/-- The canonical local pullback comparison retains the actual pulled
global section, by compatibility of the two adjunction units. -/
theorem localPullbackIso_section (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤))
    (U : Y.Opens) :
    ((Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).hom.app M).val.app
        (op ⊤) (restrictSection (f ⁻¹ᵁ U).ι ((Scheme.Modules.pullback f).obj M)
          (pullbackSection f M s)) =
      pullbackSection (f ∣_ U) (M.restrict U.ι) (restrictSection U.ι M s) := by
  let P := (Scheme.Modules.pullback f).obj M
  let e := (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).app M
  have h := congrArg (fun k => k.val.app (op (⊤ : U.toScheme.Opens))
      (restrictSection U.ι M s))
    (Scheme.Modules.Pullback.OpenRestriction.restrictedUnit f U M)
  change e.inv.val.app (op ⊤)
      (pullbackSection (f ∣_ U) (M.restrict U.ι) (restrictSection U.ι M s)) =
    (Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap f U P).val.app (op ⊤)
      (((Scheme.Modules.restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction f).unit.app M)).val.app (op ⊤)
          (restrictSection U.ι M s)) at h
  rw [Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap_apply] at h
  change e.inv.val.app (op ⊤)
      (pullbackSection (f ∣_ U) (M.restrict U.ι) (restrictSection U.ι M s)) =
    P.val.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (op (U.ι ''ᵁ ⊤))
        (M.val.map (homOfLE le_top).op s)) at h
  have hn : ((pullbackPushforwardAdjunction f).unit.app M).val.app (op (U.ι ''ᵁ ⊤))
      (M.val.map (homOfLE le_top).op s) =
      ((Scheme.Modules.pushforward f).obj P).val.map (homOfLE le_top).op
        (pullbackSection f M s) :=
    (pullbackSection_restrict f M s (U.ι ''ᵁ ⊤)).symm
  have hm : P.val.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
      (((Scheme.Modules.pushforward f).obj P).val.map (homOfLE le_top).op
        (pullbackSection f M s)) =
      restrictSection (f ⁻¹ᵁ U).ι P (pullbackSection f M s) := by
    change (P.presheaf.map ((Opens.map f.base).map (homOfLE le_top)).op ≫
      P.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)
        (pullbackSection f M s) =
      P.presheaf.map (homOfLE le_top).op (pullbackSection f M s)
    rw [← Functor.map_comp]
    rfl
  have hinv := h.trans ((congrArg
    (fun z => P.val.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op z) hn).trans hm)
  calc
    _ = e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤)
        (pullbackSection (f ∣_ U) (M.restrict U.ι) (restrictSection U.ι M s))) :=
      congrArg (fun z => e.hom.val.app (op ⊤) z) hinv.symm
    _ = _ := by
      change (e.inv ≫ e.hom).val.app (op ⊤)
        (pullbackSection (f ∣_ U) (M.restrict U.ι) (restrictSection U.ι M s)) = _
      rw [Iso.inv_hom_id]
      exact ModuleCat.id_apply _ _

/-- The actual pulled frame on the actual inverse-image open. -/
def pulledRestrictionFrame (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).app M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso d ≪≫ pullbackUnitIso (f ∣_ U)

theorem pulledRestrictionFrame_coefficient (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : Γ(M, ⊤)) :
    (pulledRestrictionFrame f M U d).hom.val.app (op ⊤)
        (restrictSection (f ⁻¹ᵁ U).ι ((Scheme.Modules.pullback f).obj M)
          (pullbackSection f M s)) =
      (f ∣_ U).appTop (d.hom.val.app (op ⊤) (restrictSection U.ι M s)) := by
  change ((Scheme.Modules.pullback (f ∣_ U)).mapIso d ≪≫
    pullbackUnitIso (f ∣_ U)).hom.val.app (op ⊤)
      (((Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).hom.app M).val.app
        (op ⊤) (restrictSection (f ⁻¹ᵁ U).ι ((Scheme.Modules.pullback f).obj M)
          (pullbackSection f M s))) = _
  rw [localPullbackIso_section]
  exact pullbackSection_unitFrame (f ∣_ U) (M.restrict U.ι) d (restrictSection U.ι M s)

/-- Arbitrary scheme pullback preserves the geometric nonvanishing open of
the canonical pulled section. No flatness or Noetherian hypothesis is used. -/
theorem nonvanishingOpen_pullback (f : X ⟶ Y) (L : LineBundle Y) (s : Γ(L.val, ⊤)) :
    nonvanishingOpen (pullbackLineBundle f L) (pullbackSection f L.val s) =
      f ⁻¹ᵁ nonvanishingOpen L s := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit Y L.val).mp L.property (f x)
  let d := frameOnRestriction L.val U e
  let d' := pulledRestrictionFrame f L.val U d
  have hlocal : (f ⁻¹ᵁ U) ⊓ nonvanishingOpen (pullbackLineBundle f L)
        (pullbackSection f L.val s) =
      (f ⁻¹ᵁ U) ⊓ f ⁻¹ᵁ nonvanishingOpen L s := by
    calc
      _ = (f ⁻¹ᵁ U).ι ''ᵁ (f ⁻¹ᵁ U).toScheme.basicOpen
          (d'.hom.val.app (op ⊤)
            (restrictSection (f ⁻¹ᵁ U).ι ((Scheme.Modules.pullback f).obj L.val)
              (pullbackSection f L.val s))) :=
        (image_basicOpen_restrictionFrame (pullbackLineBundle f L)
          (pullbackSection f L.val s) (f ⁻¹ᵁ U) d').symm
      _ = (f ⁻¹ᵁ U).ι ''ᵁ (f ∣_ U) ⁻¹ᵁ U.toScheme.basicOpen
          (d.hom.val.app (op ⊤) (restrictSection U.ι L.val s)) := by
        rw [pulledRestrictionFrame_coefficient, Scheme.preimage_basicOpen_top]
      _ = f ⁻¹ᵁ (U.ι ''ᵁ U.toScheme.basicOpen
          (d.hom.val.app (op ⊤) (restrictSection U.ι L.val s))) :=
        image_morphismRestrict_preimage f U _
      _ = _ := by
        rw [image_basicOpen_restrictionFrame L s U d]
        rfl
  have hx : x ∈ f ⁻¹ᵁ U := hxU
  constructor
  · intro hs
    have hmem : x ∈ (f ⁻¹ᵁ U) ⊓ nonvanishingOpen (pullbackLineBundle f L)
        (pullbackSection f L.val s) := ⟨hx, hs⟩
    rw [hlocal] at hmem
    exact hmem.2
  · intro hs
    have hmem : x ∈ (f ⁻¹ᵁ U) ⊓ f ⁻¹ᵁ nonvanishingOpen L s := ⟨hx, hs⟩
    rw [← hlocal] at hmem
    exact hmem.2

/-- The real restriction-to-pullback isomorphism carries the original
restriction section to the original adjunction-unit section. -/
theorem restrictSection_to_pullback (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    ((restrictFunctorIsoPullback f).app M).hom.val.app (op ⊤) (restrictSection f M s) =
      pullbackSection f M s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M
  exact congrArg (fun k => k.val.app (op ⊤) s) h

/-- Nonvanishing for the actual restricted bundle is the literal inverse
image under the original open immersion. -/
theorem nonvanishingOpen_restrictLineBundle (f : X ⟶ Y) [IsOpenImmersion f]
    (L : LineBundle Y) (s : Γ(L.val, ⊤)) :
    nonvanishingOpen (restrictLineBundle f L) (restrictSection f L.val s) =
      f ⁻¹ᵁ nonvanishingOpen L s := by
  have h := nonvanishingOpen_iso (restrictLineBundle f L) (pullbackLineBundle f L)
    ((restrictFunctorIsoPullback f).app L.val) (restrictSection f L.val s)
  have hs := restrictSection_to_pullback f (show Y.Modules from L.val) s
  exact h.symm.trans ((congrArg (nonvanishingOpen (pullbackLineBundle f L)) hs).trans
    (nonvanishingOpen_pullback f L s))

end AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing
