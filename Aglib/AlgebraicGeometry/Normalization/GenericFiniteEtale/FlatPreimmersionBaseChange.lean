/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.ComponentRecognition
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponent
public import Aglib.AlgebraicGeometry.Stalk.IntegralBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange

/-! # Original generic normalization under flat preimmersion base change

The comparison recognizes the unchanged normal pullback by its original open
cover. No smoothness or finite-presentation hypothesis is placed on the stalk
map, and no second generic-field or normalization model is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X T U V : Scheme.{u}} [IsIntegral T] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegral U] [IsIntegral V]
  (j : U ⟶ X) [IsOpenImmersion j] (b : T ⟶ X) [Flat b] [IsPreimmersion b]
  (hg : genericPoint X ∈ Set.range b)
  (jR : V ⟶ T) [IsOpenImmersion jR]
  (g : V ⟶ U) (H : IsPullback g jR j b)
  (Y : FiniteEtale U) [IsIntegral Y.obj.left]

local notation "q" => genericMap j Y.obj.hom
local notation "pR" => pullback.snd Y.obj.hom g

omit [Flat b] [IsPreimmersion b] [IsIntegral T] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral V] [IsOpenImmersion jR] in
include H hg in
/-- The original generic point belongs to the image of the actual restricted
base-change map. This does not assert local finite presentation. -/
theorem flatPreimmersionComplement_generic_mem_range : genericPoint U ∈ Set.range g := by
  obtain ⟨t, ht⟩ := hg
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := b)
    (genericPoint U) t ((Scheme.map_genericPoint_of_isDominant U j).trans ht.symm)
  refine ⟨H.isoPullback.inv w, ?_⟩
  have he := congrArg (fun k : pullback j b ⟶ U => k w) H.isoPullback_inv_fst
  exact he.trans hw

omit [IsIntegral T] [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral V] [IsOpenImmersion jR] in
include H hg in
/-- The literal restricted cover is integral. -/
theorem flatPreimmersionBaseChange_cover_isIntegral :
    IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left := by
  let : Flat g := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsPreimmersion g := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  exact isIntegral_pullback_of_flat_preimmersion Y.obj.hom g
    (flatPreimmersionComplement_generic_mem_range j b hg jR g H)

/-- The actual open-cover map into the original flat-preimmersion pullback. -/
def flatPreimmersionBaseChangeInclusion :
    pullback Y.obj.hom g ⟶ pullback (q).fromNormalization b :=
  pullback.lift (pullback.fst _ _ ≫ inclusion j Y.obj.hom) (pR ≫ jR) (by
    rw [Category.assoc, inclusion_over, ← Category.assoc, pullback.condition,
      Category.assoc, H.w, Category.assoc])

omit [IsIntegral T] [Flat b] [IsPreimmersion b]
  [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
@[reassoc (attr := simp)] theorem flatPreimmersionBaseChangeInclusion_fst :
    flatPreimmersionBaseChangeInclusion j b jR g H Y ≫ pullback.fst (q).fromNormalization b =
      pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom := pullback.lift_fst ..

omit [IsIntegral T] [Flat b] [IsPreimmersion b]
  [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
@[reassoc (attr := simp)] theorem flatPreimmersionBaseChangeInclusion_snd :
    flatPreimmersionBaseChangeInclusion j b jR g H Y ≫ pullback.snd (q).fromNormalization b =
      pR ≫ jR := pullback.lift_snd ..

omit [IsIntegral T] [Flat b] [IsPreimmersion b]
  [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
/-- The same actual restricted cover is the base-open pullback of the unchanged
normalization's flat-preimmersion pullback. -/
theorem flatPreimmersionBaseChangeInclusion_isPullback :
    IsPullback (flatPreimmersionBaseChangeInclusion j b jR g H Y) pR
      (pullback.snd (q).fromNormalization b) jR := by
  have ho := (IsPullback.of_hasPullback Y.obj.hom g).paste_horiz (isPullback j Y.obj.hom)
  rw [H.w] at ho
  apply IsPullback.of_right (h₁₂ := pullback.fst (q).fromNormalization b)
    (h₂₂ := b) _ (flatPreimmersionBaseChangeInclusion_snd j b jR g H Y)
    (IsPullback.of_hasPullback (q).fromNormalization b)
  rw [flatPreimmersionBaseChangeInclusion_fst]
  exact ho

omit [IsIntegral T] in
include hg in
/-- The original normalization pullback has integral normal source. -/
theorem flatPreimmersionBaseChange_integral_normal :
    IsIntegral (pullback (q).fromNormalization b) ∧
      NormalStalks (pullback (q).fromNormalization b) := by
  let : IsIntegral (genericCover j Y.obj.hom).obj.left :=
    IsIntegral.of_isIso (originalFieldSpectrumIso j Y).hom
  let : IsIntegral (q).normalization := inferInstance
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsDominant (q) := by
    let : IsDominant ((originalFieldSpectrumIso j Y).hom ≫ (q)) := by
      rw [originalFieldSpectrumIso_hom_genericMap]
      infer_instance
    exact IsDominant.of_comp (originalFieldSpectrumIso j Y).hom (q)
  let : IsDominant (q).fromNormalization := by
    let : IsDominant ((q).toNormalization ≫ (q).fromNormalization) := by
      simpa only [Hom.toNormalization_fromNormalization] using
        (inferInstance : IsDominant (q))
    exact IsDominant.of_comp (q).toNormalization (q).fromNormalization
  exact ⟨isIntegral_pullback_of_flat_preimmersion (q).fromNormalization b hg,
    normalStalks_pullback_of_flat_preimmersion (q).fromNormalization b
      (genericMap_normalStalks j Y.obj.hom)⟩

local instance flatPreimmersionBaseChange_originalFinite : IsFinite (q).fromNormalization :=
  fromNormalization_isFinite j Y.obj.hom

local instance flatPreimmersionBaseChange_inclusionOpen :
    IsOpenImmersion (flatPreimmersionBaseChangeInclusion j b jR g H Y) :=
  MorphismProperty.of_isPullback (flatPreimmersionBaseChangeInclusion_isPullback j b jR g H Y).flip
    inferInstance

/-- The comparison is constructed from the actual dense open and normal
pullback; it is not a normalization base-change hypothesis. -/
def flatPreimmersionBaseChangeIso :
    (genericMap jR pR).normalization ≅ pullback (q).fromNormalization b := by
  let : IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jR g H Y
  let : IsIntegral (pullback (q).fromNormalization b) :=
    (flatPreimmersionBaseChange_integral_normal j b hg Y).1
  exact componentRecognitionIso jR ((FiniteEtale.baseChange g).obj Y)
    (flatPreimmersionBaseChange_integral_normal j b hg Y).2
    (pullback.snd (q).fromNormalization b) (flatPreimmersionBaseChangeInclusion j b jR g H Y)
    (flatPreimmersionBaseChangeInclusion_snd j b jR g H Y)

@[reassoc (attr := simp)] theorem flatPreimmersionBaseChangeIso_hom_over :
    (flatPreimmersionBaseChangeIso j b hg jR g H Y).hom ≫ pullback.snd (q).fromNormalization b =
      (genericMap jR pR).fromNormalization := by
  let : IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jR g H Y
  let : IsIntegral (pullback (q).fromNormalization b) :=
    (flatPreimmersionBaseChange_integral_normal j b hg Y).1
  have h := componentRecognitionIso_hom_over jR ((FiniteEtale.baseChange g).obj Y)
    (flatPreimmersionBaseChange_integral_normal j b hg Y).2
    (pullback.snd (q).fromNormalization b) (flatPreimmersionBaseChangeInclusion j b jR g H Y)
    (flatPreimmersionBaseChangeInclusion_snd j b jR g H Y)
  exact h

@[reassoc (attr := simp)] theorem flatPreimmersionBaseChangeIso_hom_generic :
    (genericMap jR pR).toNormalization ≫ (flatPreimmersionBaseChangeIso j b hg jR g H Y).hom =
      genericToCover jR pR ≫ flatPreimmersionBaseChangeInclusion j b jR g H Y := by
  let : IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jR g H Y
  let : IsIntegral (pullback (q).fromNormalization b) :=
    (flatPreimmersionBaseChange_integral_normal j b hg Y).1
  have h := componentRecognitionIso_hom_generic jR ((FiniteEtale.baseChange g).obj Y)
    (flatPreimmersionBaseChange_integral_normal j b hg Y).2
    (pullback.snd (q).fromNormalization b) (flatPreimmersionBaseChangeInclusion j b jR g H Y)
    (flatPreimmersionBaseChangeInclusion_snd j b jR g H Y)
  exact h

omit [IsIntegral T] [IsIntegral X] [IsLocallyNoetherian X] in
include b in
/-- Normal stalks transfer along the original flat preimmersion stalk-map isomorphisms. -/
theorem flatPreimmersionBaseChange_baseNormal :
    ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
  fun z => by
    let : IsIso (b.stalkMap z) :=
      Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks b z
    exact IsIntegrallyClosed.of_equiv (asIso (b.stalkMap z)).commRingCatIsoToRingEquiv

/-- The original covering-source comparison is retained on the nose. -/
@[reassoc (attr := simp)] theorem inclusion_flatPreimmersionBaseChangeIso_hom :
    letI : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
      flatPreimmersionBaseChange_baseNormal b
    inclusion jR pR ≫ (flatPreimmersionBaseChangeIso j b hg jR g H Y).hom =
      flatPreimmersionBaseChangeInclusion j b jR g H Y := by
  let : IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jR g H Y
  let : IsIntegral (pullback (q).fromNormalization b) :=
    (flatPreimmersionBaseChange_integral_normal j b hg Y).1
  let : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    flatPreimmersionBaseChange_baseNormal b
  have h := inclusion_componentRecognitionIso_hom jR ((FiniteEtale.baseChange g).obj Y)
    (flatPreimmersionBaseChange_integral_normal j b hg Y).2
    (pullback.snd (q).fromNormalization b) (flatPreimmersionBaseChangeInclusion j b jR g H Y)
    (flatPreimmersionBaseChangeInclusion_snd j b jR g H Y)
  exact h

omit [IsIntegral T] [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsOpenImmersion jR] in
include H hg in
/-- Connected base change retains Galoisness and the exact original deck order. -/
theorem flatPreimmersionBaseChange_galois_card [CategoryTheory.PreGaloisCategory.IsGalois Y] :
    CategoryTheory.PreGaloisCategory.IsGalois ((FiniteEtale.baseChange g).obj Y) ∧
      Nat.card (Aut ((FiniteEtale.baseChange g).obj Y)) = Nat.card (Aut Y) := by
  let : IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
    flatPreimmersionBaseChange_cover_isIntegral j b hg jR g H Y
  exact ⟨baseChange_isGalois_of_connected g Y, baseChange_card_aut_of_connected g Y⟩

/-- The original whole section, not a newly chosen point, determines the local
section and its original closed-point comparison. -/
theorem exists_flatPreimmersionBaseChangeSection {D : Type u} [CommRing D] [IsLocalRing D]
    (s : Spec (.of D) ⟶ (q).normalization)
    (r : Spec (.of D) ⟶ T)
    (hs : s ≫ (q).fromNormalization = r ≫ b) :
    ∃ sR : Spec (.of D) ⟶ (genericMap jR pR).normalization,
      sR ≫ (genericMap jR pR).fromNormalization = r ∧
      sR ≫ (flatPreimmersionBaseChangeIso j b hg jR g H Y).hom ≫
        pullback.fst (q).fromNormalization b = s ∧
      ((flatPreimmersionBaseChangeIso j b hg jR g H Y).hom ≫
        pullback.fst (q).fromNormalization b) (sR (IsLocalRing.closedPoint D)) =
          s (IsLocalRing.closedPoint D) := by
  let d := pullback.lift s r hs
  let e := flatPreimmersionBaseChangeIso j b hg jR g H Y
  let sR := d ≫ e.inv
  have he : sR ≫ e.hom = d := by simp [sR]
  have hfst : sR ≫ e.hom ≫ pullback.fst (q).fromNormalization b = s := by
    rw [← Category.assoc, he, pullback.lift_fst]
  refine ⟨sR, ?_, hfst, ?_⟩
  · rw [← flatPreimmersionBaseChangeIso_hom_over j b hg jR g H Y, ← Category.assoc, he]
    exact pullback.lift_snd ..
  · exact congrArg (fun k : Spec (.of D) ⟶ (q).normalization =>
      k (IsLocalRing.closedPoint D)) hfst

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
