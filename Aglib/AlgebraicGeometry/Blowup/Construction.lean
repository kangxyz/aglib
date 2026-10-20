/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Construction of universal blowups from actual affine local data

Affine local data are supplied by the original saturated Rees Proj construction.
The canonical maps for inclusions of affine opens are cartesian open immersions;
universal uniqueness gives their coherence. Native locally directed scheme gluing
then constructs the global object without an existence or gluing family as input.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- A universal blowup for an actual ideal sheaf on an affine scheme, using the canonical
spectrum isomorphism and the original affine Rees Proj construction. -/
def affineDatum {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) : BlowupDatum I where
  Y := (spectrumDatum (I.comap X.isoSpec.inv)).Y
  map := (spectrumDatum (I.comap X.isoSpec.inv)).map ≫ X.isoSpec.inv
  cartier := by
    unfold cartierPullback
    rw [Scheme.IdealSheafData.comap_comp]
    exact (spectrumDatum (I.comap X.isoSpec.inv)).cartier
  universal T f hf := by
    let B := spectrumDatum (I.comap X.isoSpec.inv)
    have hf' : cartierPullback (I.comap X.isoSpec.inv) (f ≫ X.isoSpec.hom) := by
      unfold cartierPullback
      rw [← Scheme.IdealSheafData.comap_comp, Category.assoc, X.isoSpec.hom_inv_id,
        Category.comp_id]
      exact hf
    obtain ⟨g, hg, huniq⟩ := B.universal T (f ≫ X.isoSpec.hom) hf'
    refine ⟨g, ?_, ?_⟩
    · change g ≫ B.map ≫ X.isoSpec.inv = f
      rw [← Category.assoc, hg, Category.assoc, X.isoSpec.hom_inv_id, Category.comp_id]
    · intro k hk
      apply huniq k
      apply (cancel_mono X.isoSpec.inv).mp
      simpa only [Category.assoc, X.isoSpec.hom_inv_id, Category.comp_id] using hk

namespace Construction

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual universal datum of the inverse-image centre on an affine open of the base. -/
def localDatum (U : X.affineOpens) : BlowupDatum (I.comap U.1.ι) := by
  let : IsAffine U.1.toScheme := U.2
  exact affineDatum (I.comap U.1.ι)

/-- The original centre equality for an inclusion of actual affine base opens. -/
theorem localCentre {U V : X.affineOpens} (h : U ⟶ V) :
    (I.comap V.1.ι).comap (X.homOfLE h.le) = I.comap U.1.ι := by
  rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]

/-- The canonical morphism of actual local blowups for an inclusion of affine base opens. -/
def localMap {U V : X.affineOpens} (h : U ⟶ V) :
    (localDatum I U).Y ⟶ (localDatum I V).Y :=
  BaseChange.map (X.homOfLE h.le) (localCentre I h) (localDatum I V) (localDatum I U)

@[reassoc (attr := simp)]
theorem localMap_triangle {U V : X.affineOpens} (h : U ⟶ V) :
    localMap I h ≫ (localDatum I V).map = (localDatum I U).map ≫ X.homOfLE h.le :=
  BaseChange.map_triangle _ _ _ _

/-- The canonical local map is the actual cartesian comparison for the affine-open inclusion. -/
theorem localMap_isPullback {U V : X.affineOpens} (h : U ⟶ V) :
    IsPullback (localMap I h) (localDatum I U).map (localDatum I V).map
      (X.homOfLE h.le) :=
  BaseChange.isPullback_of_flat _ inferInstance _ _ _

instance localMap_isOpenImmersion {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion (localMap I h) :=
  MorphismProperty.of_isPullback (localMap_isPullback I h).flip inferInstance

@[simp]
theorem localMap_id (U : X.affineOpens) : localMap I (𝟙 U) = 𝟙 (localDatum I U).Y := by
  apply (localDatum I U).hom_ext (localDatum I U).cartier
  · rw [localMap_triangle, Scheme.homOfLE_rfl, Category.comp_id]
  · exact Category.id_comp _

@[reassoc]
theorem localMap_comp {U V W : X.affineOpens} (h : U ⟶ V) (k : V ⟶ W) :
    localMap I h ≫ localMap I k = localMap I (h ≫ k) := by
  apply (localDatum I W).hom_ext
    (BaseChange.cartier_composite (X.homOfLE (h ≫ k).le)
      (localCentre I (h ≫ k)) (localDatum I U))
  · rw [Category.assoc, localMap_triangle, ← Category.assoc, localMap_triangle,
      Category.assoc, Scheme.homOfLE_homOfLE]
  · exact localMap_triangle I (h ≫ k)

/-- The functor of actual affine local blowups and canonical maps for inclusions. -/
def diagram : X.affineOpens ⥤ Scheme.{u} where
  obj U := (localDatum I U).Y
  map h := localMap I h
  map_id := localMap_id I
  map_comp h k := (localMap_comp I h k).symm

instance diagramMap_isOpenImmersion {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion ((diagram I).map h) := localMap_isOpenImmersion I h

/-- The image of a canonical local transition is the actual inverse image of its base open. -/
theorem localMap_opensRange {U V : X.affineOpens} (h : U ⟶ V) :
    (localMap I h).opensRange = (localDatum I V).map ⁻¹ᵁ (X.homOfLE h.le).opensRange := by
  calc
    _ = ((localMap_isPullback I h).isoPullback.hom ≫
        pullback.fst (localDatum I V).map (X.homOfLE h.le)).opensRange := by
      congr 1
      exact (localMap_isPullback I h).isoPullback_hom_fst.symm
    _ = _ := by rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]

/-- A point whose actual base point belongs to the smaller affine open lifts through the
canonical local transition. -/
theorem mem_range_localMap {U V : X.affineOpens} (h : U ⟶ V)
    (y : (localDatum I V).Y) (hy : ((localDatum I V).map y).1 ∈ U.1) :
    y ∈ Set.range (localMap I h) := by
  change y ∈ (localMap I h).opensRange
  rw [localMap_opensRange]
  refine ⟨⟨((localDatum I V).map y).1, hy⟩, ?_⟩
  exact Subtype.ext (congrArg Subtype.val (X.homOfLE_apply' h.le _ hy))

/-- The original structural maps form a cocone from the affine local blowups to the base. -/
def baseCocone : Cocone (diagram I) where
  pt := X
  ι.app U := (localDatum I U).map ≫ U.1.ι
  ι.naturality {U V} h := by
    change localMap I h ≫ ((localDatum I V).map ≫ V.1.ι) =
      ((localDatum I U).map ≫ U.1.ι) ≫ 𝟙 X
    rw [← Category.assoc, localMap_triangle, Category.assoc, Scheme.homOfLE_ι,
      Category.comp_id]

private theorem localMap_base {U V : X.affineOpens} (h : U ⟶ V) :
    localMap I h ≫ ((localDatum I V).map ≫ V.1.ι) = (localDatum I U).map ≫ U.1.ι := by
  rw [← Category.assoc, localMap_triangle, Category.assoc, Scheme.homOfLE_ι]

instance diagramIsLocallyDirected : ((diagram I) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W hUW hVW xi xj h
  change localMap I hUW xi = localMap I hVW xj at h
  have hroot : ((localDatum I U).map xi).1 = ((localDatum I V).map xj).1 := by
    calc
      _ = (localMap I hUW ≫ ((localDatum I W).map ≫ W.1.ι)) xi :=
        (congrArg (fun k => k xi) (localMap_base I hUW)).symm
      _ = (localMap I hVW ≫ ((localDatum I W).map ≫ W.1.ι)) xj :=
        congrArg ((localDatum I W).map ≫ W.1.ι) h
      _ = _ := congrArg (fun k => k xj) (localMap_base I hVW)
  obtain ⟨L, hL, hxL, hLUV⟩ := exists_isAffineOpen_mem_and_subset
    (show ((localDatum I U).map xi).1 ∈ U.1 ⊓ V.1 from
      ⟨((localDatum I U).map xi).2, hroot ▸ ((localDatum I V).map xj).2⟩)
  let l : X.affineOpens := ⟨L, hL⟩
  let fli : l ⟶ U := homOfLE (hLUV.trans inf_le_left)
  let flj : l ⟶ V := homOfLE (hLUV.trans inf_le_right)
  obtain ⟨z, hz⟩ := mem_range_localMap I fli xi hxL
  refine ⟨l, fli, flj, z, hz, ?_⟩
  apply (localMap I hVW).isOpenEmbedding.injective
  have heq : fli ≫ hUW = flj ≫ hVW := Subsingleton.elim _ _
  calc
    localMap I hVW (localMap I flj z) = localMap I (flj ≫ hVW) z := by
      rw [← localMap_comp]
      rfl
    _ = localMap I (fli ≫ hUW) z := by rw [heq]
    _ = localMap I hUW (localMap I fli z) := by
      rw [← localMap_comp]
      rfl
    _ = localMap I hVW xj := by rw [hz, h]

/-- The native locally directed gluing of the actual affine local blowups. -/
def obj : Scheme.{u} := colimit (diagram I)

/-- The actual structural map of the glued local blowups to the original base scheme. -/
def map : obj I ⟶ X := colimit.desc (diagram I) (baseCocone I)

@[reassoc (attr := simp)]
theorem ι_map (U : X.affineOpens) :
    colimit.ι (diagram I) U ≫ map I = (localDatum I U).map ≫ U.1.ι :=
  colimit.ι_desc (baseCocone I) U

/-- The inverse image of an actual affine base open is exactly its local blowup chart
in the native gluing. -/
theorem map_preimage (U : X.affineOpens) :
    map I ⁻¹ᵁ U.1 = (colimit.ι (diagram I) U).opensRange := by
  ext y
  change map I y ∈ U.1 ↔ ∃ z, colimit.ι (diagram I) U z = y
  constructor
  · intro hy
    obtain ⟨V, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram I) y
    change (colimit.ι (diagram I) V ≫ map I) z ∈ U.1 at hy
    rw [ι_map] at hy
    change ((localDatum I V).map z).1 ∈ U.1 at hy
    obtain ⟨L, hL, hxL, hLUV⟩ := exists_isAffineOpen_mem_and_subset
      (show ((localDatum I V).map z).1 ∈ U.1 ⊓ V.1 from
        ⟨hy, ((localDatum I V).map z).2⟩)
    let l : X.affineOpens := ⟨L, hL⟩
    let fli : l ⟶ U := homOfLE (hLUV.trans inf_le_left)
    let flj : l ⟶ V := homOfLE (hLUV.trans inf_le_right)
    obtain ⟨w, hw⟩ := mem_range_localMap I flj z hxL
    refine ⟨localMap I fli w, ?_⟩
    calc
      colimit.ι (diagram I) U (localMap I fli w) = colimit.ι (diagram I) l w :=
        congrArg (fun k => k w) (colimit.w (diagram I) fli)
      _ = colimit.ι (diagram I) V (localMap I flj w) :=
        (congrArg (fun k => k w) (colimit.w (diagram I) flj)).symm
      _ = colimit.ι (diagram I) V z := by rw [hw]
  · rintro ⟨z, rfl⟩
    change (colimit.ι (diagram I) U ≫ map I) z ∈ U.1
    rw [ι_map]
    exact ((localDatum I U).map z).2

/-- Every affine local blowup is the actual pullback of the glued scheme over its base open. -/
theorem local_isPullback (U : X.affineOpens) :
    IsPullback (localDatum I U).map (colimit.ι (diagram I) U) U.1.ι (map I) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι_map I U)
    (by simpa only [Scheme.Opens.opensRange_ι] using map_preimage I U)

/-- The original centre has Cartier actual inverse image on the constructed glued scheme. -/
theorem cartier : cartierPullback I (map I) := by
  unfold cartierPullback
  apply Scheme.Modules.Invertible.isLocallyRankOne_of_forall_isLocallyRankOneAt
  intro y
  obtain ⟨U, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram I) y
  let e := colimit.ι (diagram I) U
  let J := I.comap (map I)
  let i := J.subschemeι
  let i' := (J.comap e).subschemeι
  let a := (J.comap e).subschemeMap J e (J.le_map_comap e)
  have h : a ≫ i = i' ≫ e := Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have H : IsPullback a i' i e :=
    (isPullback_of_isClosedImmersion i' i a e h.symm (by simp [i, i'])).flip
  have : IsIso (Scheme.Hom.idealPullbackMap i i' e a h) :=
    Scheme.Hom.idealPullbackMap_isIso_of_isOpenImmersion i i' e a h H
  have hlocal : Scheme.Modules.Invertible.IsLocallyRankOne (localDatum I U).Y
      (Scheme.Hom.idealModule i') := by
    change Scheme.Modules.Invertible.IsLocallyRankOne (localDatum I U).Y
      (Scheme.Hom.idealModule (J.comap e).subschemeι)
    have heq : J.comap e = (I.comap U.1.ι).comap (localDatum I U).map := by
      dsimp only [J, e]
      rw [← Scheme.IdealSheafData.comap_comp, ι_map, Scheme.IdealSheafData.comap_comp]
    rw [heq]
    exact (localDatum I U).cartier
  exact ⟨(localDatum I U).Y, e, inferInstance, ⟨z, rfl⟩,
    Scheme.Modules.Invertible.isLocallyRankOne_of_iso _
      (asIso (Scheme.Hom.idealPullbackMap i i' e a h)).symm hlocal⟩

/-- The actual open cover of a scheme by all its affine open subschemes. -/
def baseCover (X : Scheme.{u}) : X.OpenCover where
  I₀ := X.affineOpens
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨U, hU⟩, ⟨⟨x, hxU⟩, rfl⟩⟩

/-- The Cartier premise of a test map restricts to the literal pullback over an affine
base open, for the original inverse-image centre on that open. -/
theorem cartierOnBaseOpen {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U : X.affineOpens) :
    cartierPullback (I.comap U.1.ι) (pullback.snd f U.1.ι) := by
  have h := cartierPullback_comp_of_flat I f hf (pullback.fst f U.1.ι)
  unfold cartierPullback at h ⊢
  rw [pullback.condition, Scheme.IdealSheafData.comap_comp] at h
  exact h

/-- Maps into the actual glued scheme are unique over the base whenever the original
inverse-image centre is Cartier. This uses the proved local pullback squares. -/
theorem hom_ext {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    {g h : T ⟶ obj I} (hg : g ≫ map I = f) (hh : h ≫ map I = f) : g = h := by
  apply Cover.hom_ext ((baseCover X).pullback₁ f)
  intro U
  change pullback.fst f U.1.ι ≫ g = pullback.fst f U.1.ι ≫ h
  let H := local_isPullback I U
  have hgc : pullback.snd f U.1.ι ≫ U.1.ι = (pullback.fst f U.1.ι ≫ g) ≫ map I := by
    rw [Category.assoc, hg]
    exact pullback.condition.symm
  have hhc : pullback.snd f U.1.ι ≫ U.1.ι = (pullback.fst f U.1.ι ≫ h) ≫ map I := by
    rw [Category.assoc, hh]
    exact pullback.condition.symm
  let gu := H.lift (pullback.snd f U.1.ι) (pullback.fst f U.1.ι ≫ g) hgc
  let hu := H.lift (pullback.snd f U.1.ι) (pullback.fst f U.1.ι ≫ h) hhc
  have heq : gu = hu := (localDatum I U).hom_ext (cartierOnBaseOpen I f hf U)
    (H.lift_fst _ _ _) (H.lift_fst _ _ _)
  calc
    pullback.fst f U.1.ι ≫ g = gu ≫ colimit.ι (diagram I) U := (H.lift_snd _ _ _).symm
    _ = hu ≫ colimit.ι (diagram I) U := by rw [heq]
    _ = pullback.fst f U.1.ι ≫ h := H.lift_snd _ _ _

/-- The actual universal lift on the literal pullback of a test scheme over an affine base open. -/
def localLift {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f) (U : X.affineOpens) :
    pullback f U.1.ι ⟶ (localDatum I U).Y :=
  (localDatum I U).lift (pullback.snd f U.1.ι) (cartierOnBaseOpen I f hf U)

@[reassoc (attr := simp)]
theorem localLift_map {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U : X.affineOpens) : localLift I f hf U ≫ (localDatum I U).map = pullback.snd f U.1.ι :=
  (localDatum I U).lift_map _ _

/-- The actual local map from a test scheme into the constructed glued scheme. -/
def localToGlued {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U : X.affineOpens) : pullback f U.1.ι ⟶ obj I :=
  localLift I f hf U ≫ colimit.ι (diagram I) U

@[reassoc]
theorem localToGlued_map {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U : X.affineOpens) : localToGlued I f hf U ≫ map I = pullback.fst f U.1.ι ≫ f := by
  rw [localToGlued, Category.assoc, ι_map, ← Category.assoc, localLift_map,
    pullback.condition]

/-- The actual local universal lifts agree on literal overlaps of the pulled-back base cover. -/
theorem localToGlued_compat {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U V : X.affineOpens) :
    pullback.fst (pullback.fst f U.1.ι) (pullback.fst f V.1.ι) ≫ localToGlued I f hf U =
      pullback.snd _ _ ≫ localToGlued I f hf V := by
  let C := (baseCover X).pullback₁ f
  let e := pullback.fst (C.f U) (C.f V) ≫ C.f U
  have he : cartierPullback I (e ≫ f) := cartierPullback_comp_of_flat I f hf e
  apply hom_ext I (e ≫ f) he
  · rw [Category.assoc, localToGlued_map]
    rfl
  · rw [Category.assoc, localToGlued_map]
    change pullback.snd (C.f U) (C.f V) ≫ C.f V ≫ f = e ≫ f
    simpa only [e, Category.assoc] using
      (congrArg (fun k => k ≫ f) (pullback.condition (f := C.f U) (g := C.f V))).symm

/-- The universal map to the constructed global blowup, glued from the actual local lifts. -/
def lift {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f) : T ⟶ obj I :=
  Cover.glueMorphisms ((baseCover X).pullback₁ f) (localToGlued I f hf)
    (localToGlued_compat I f hf)

/-- Restriction of the glued universal map is the original local universal lift. -/
theorem baseCover_lift {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f)
    (U : X.affineOpens) : pullback.fst f U.1.ι ≫ lift I f hf = localToGlued I f hf U :=
  Cover.ι_glueMorphisms ((baseCover X).pullback₁ f) (localToGlued I f hf)
    (localToGlued_compat I f hf) U

@[reassoc (attr := simp)]
theorem lift_map {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f) :
    lift I f hf ≫ map I = f := by
  apply Cover.hom_ext ((baseCover X).pullback₁ f)
  intro U
  change (pullback.fst f U.1.ι ≫ lift I f hf) ≫ map I = pullback.fst f U.1.ι ≫ f
  rw [baseCover_lift, localToGlued_map]

/-- The final-object property of the actual glued blowup, for every test scheme with
the original Cartier inverse-image centre. -/
theorem universal (T : Scheme.{u}) (f : T ⟶ X) (hf : cartierPullback I f) :
    ∃! g : T ⟶ obj I, g ≫ map I = f :=
  ⟨lift I f hf, lift_map I f hf, fun _ hg => hom_ext I f hf hg (lift_map I f hf)⟩

end Construction

/-- The actual global universal blowup of an ideal sheaf, constructed by native gluing
of its actual saturated affine local blowups. -/
def blowupDatum {X : Scheme.{u}} (I : X.IdealSheafData) : BlowupDatum I where
  Y := Construction.obj I
  map := Construction.map I
  cartier := Construction.cartier I
  universal := Construction.universal I

/-- The exact original locally Noetherian existence family is supplied by the actual
global construction. The construction itself requires no additional Noetherian premise. -/
theorem noetherianBlowupExistence : NoetherianBlowupExistence.{u} := by
  intro X _ I
  exact ⟨blowupDatum I⟩

end AlgebraicGeometry.Scheme.Blowup
