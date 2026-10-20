/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper modifications by open pushouts

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.ProperModification`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `07f2d278ce0172f78cc7b04fff0f15781dedacae3c2fd5357ccac692210c6679`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section AlgebraicGeometry.Scheme.OpenPushout.Modification


noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OpenPushout.Modification


section GluedMap
variable {A Y U V X : Scheme.{u}} (f : A ⟶ Y) (g : A ⟶ V)
  [IsOpenImmersion f] [IsOpenImmersion g]
  (p : Y ⟶ U) (i : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (w : f ≫ (p ≫ i) = g ≫ j)

def gluedMap : pushout f g ⟶ X := pushout.desc (p ≫ i) j w

omit [IsOpenImmersion i] [IsOpenImmersion j] in
@[reassoc (attr := simp)] lemma inl_gluedMap :
    pushout.inl f g ≫ gluedMap f g p i j w = p ≫ i := by
  exact pushout.inl_desc (p ≫ i) j w
omit [IsOpenImmersion i] [IsOpenImmersion j] in
@[reassoc (attr := simp)] lemma inr_gluedMap :
    pushout.inr f g ≫ gluedMap f g p i j w = j := by
  exact pushout.inr_desc (p ≫ i) j w

omit [IsOpenImmersion i] [IsOpenImmersion j] in
lemma preimage_range_inl (hg : Set.range g = j ⁻¹' Set.range i) :
    gluedMap f g p i j w ⁻¹' Set.range i = Set.range (pushout.inl f g) := by
  ext z
  constructor
  · intro hz
    rcases openPushout_covered f g z with ⟨y, rfl⟩ | ⟨v, rfl⟩
    · exact ⟨y, rfl⟩
    · have hv : v ∈ Set.range g := by
        rw [hg]
        simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, inr_gluedMap] using hz
      obtain ⟨a, rfl⟩ := hv
      exact ⟨f a, by simp only [← Scheme.Hom.comp_apply, pushout.condition]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨p y, by simp only [← Scheme.Hom.comp_apply, inl_gluedMap]⟩

omit [IsOpenImmersion i] [IsOpenImmersion j] in
lemma preimage_range_inr (hf : Set.range f = (p ≫ i) ⁻¹' Set.range j) :
    gluedMap f g p i j w ⁻¹' Set.range j = Set.range (pushout.inr f g) := by
  ext z
  constructor
  · intro hz
    rcases openPushout_covered f g z with ⟨y, rfl⟩ | ⟨v, rfl⟩
    · have hy : y ∈ Set.range f := by
        rw [hf]
        simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, inl_gluedMap] using hz
      obtain ⟨a, rfl⟩ := hy
      exact ⟨g a, by simp only [← Scheme.Hom.comp_apply, pushout.condition]⟩
    · exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp only [← Scheme.Hom.comp_apply, inr_gluedMap]⟩

omit [IsOpenImmersion j] in
lemma inl_isPullback [IsOpenImmersion j] (hg : Set.range g = j ⁻¹' Set.range i) :
    IsPullback p (pushout.inl f g) i (gluedMap f g p i j w) := by
  apply IsOpenImmersion.isPullback
  · simp
  · exact TopologicalSpace.Opens.ext (preimage_range_inl f g p i j w hg)

omit [IsOpenImmersion i] in
lemma inr_isPullback [IsOpenImmersion i] (hf : Set.range f = (p ≫ i) ⁻¹' Set.range j) :
    IsPullback (𝟙 V) (pushout.inr f g) j (gluedMap f g p i j w) := by
  apply IsOpenImmersion.isPullback
  · simp
  · exact TopologicalSpace.Opens.ext (preimage_range_inr f g p i j w hf)

lemma isProper_gluedMap [IsProper p]
    (hf : Set.range f = (p ≫ i) ⁻¹' Set.range j)
    (hg : Set.range g = j ⁻¹' Set.range i)
    (hcover : i.opensRange ⊔ j.opensRange = ⊤) :
    IsProper (gluedMap f g p i j w) := by
  have hleft : IsProper (pullback.snd (gluedMap f g p i j w) i) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
      (inl_isPullback f g p i j w hg).flip.isoPullback.hom]
    simpa using (inferInstance : IsProper p)
  have hright : IsProper (pullback.snd (gluedMap f g p i j w) j) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
      (inr_isPullback f g p i j w hf).flip.isoPullback.hom]
    simpa using (inferInstance : IsProper (𝟙 V))
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun b : Bool => if b then i.opensRange else j.opensRange)
  · simpa only [iSup_bool_eq, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false]
      using hcover
  · intro b
    cases b
    · exact (MorphismProperty.arrow_mk_iso_iff (@IsProper)
        (morphismRestrictOpensRange _ j)).mpr hright
    · exact (MorphismProperty.arrow_mk_iso_iff (@IsProper)
        (morphismRestrictOpensRange _ i)).mpr hleft
end GluedMap

/-- The image of the restriction of an open immersion is the other side
of the same ordinary intersection. -/
lemma range_openImmersion_restrict {U X : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] (V : X.Opens) :
    Set.range (i ∣_ V) = V.ι ⁻¹' Set.range i := by
  unfold morphismRestrict
  change Set.range ((pullback.snd i V.ι) ∘ (pullbackRestrictIsoRestrict i V).inv) = _
  have hs : Function.Surjective (pullbackRestrictIsoRestrict i V).inv :=
    (pullbackRestrictIsoRestrict i V).inv.homeomorph.surjective
  rw [hs.range_comp]
  exact IsOpenImmersion.range_pullbackSnd i V.ι

/- Direct replacement of a chart presented as an arbitrary open immersion.
This avoids transporting a recursive source along an isomorphism onto its range. -/
namespace OfRestriction
variable {Y U X : Scheme.{u}} (p : Y ⟶ U) (i : U ⟶ X)
  [IsOpenImmersion i] (V : X.Opens) [IsIso (p ∣_ (i ⁻¹ᵁ V))]

abbrev overlap : Scheme.{u} := (p ⁻¹ᵁ (i ⁻¹ᵁ V)).toScheme
abbrev overlapToModified : overlap p i V ⟶ Y := (p ⁻¹ᵁ (i ⁻¹ᵁ V)).ι

def overlapToUnchanged : overlap p i V ⟶ V := (p ∣_ (i ⁻¹ᵁ V)) ≫ (i ∣_ V)

instance overlapToUnchanged_isOpenImmersion :
    IsOpenImmersion (overlapToUnchanged p i V) := by
  dsimp [overlapToUnchanged]
  infer_instance

omit [IsOpenImmersion i] [IsIso (p ∣_ (i ⁻¹ᵁ V))] in
lemma overlap_triangle : overlapToModified p i V ≫ (p ≫ i) =
    overlapToUnchanged p i V ≫ V.ι := by
  simp only [overlapToUnchanged, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc]

omit [IsOpenImmersion i] [IsIso (p ∣_ (i ⁻¹ᵁ V))] in
lemma range_overlapToModified : Set.range (overlapToModified p i V) =
    (p ≫ i) ⁻¹' Set.range V.ι := by
  simp only [overlapToModified, Scheme.Opens.range_ι]
  rfl

lemma range_overlapToUnchanged : Set.range (overlapToUnchanged p i V) =
    V.ι ⁻¹' Set.range i := by
  change Set.range ((i ∣_ V) ∘ (p ∣_ (i ⁻¹ᵁ V))) = _
  have hs : Function.Surjective (p ∣_ (i ⁻¹ᵁ V)) :=
    (p ∣_ (i ⁻¹ᵁ V)).homeomorph.surjective
  rw [hs.range_comp]
  exact range_openImmersion_restrict i V

abbrev glued : Scheme.{u} := pushout (overlapToModified p i V) (overlapToUnchanged p i V)

def map : glued p i V ⟶ X := gluedMap (overlapToModified p i V)
  (overlapToUnchanged p i V) p i V.ι (overlap_triangle p i V)

abbrev modifiedChart : Y ⟶ glued p i V :=
  pushout.inl (overlapToModified p i V) (overlapToUnchanged p i V)
abbrev unchangedChart : V.toScheme ⟶ glued p i V :=
  pushout.inr (overlapToModified p i V) (overlapToUnchanged p i V)

instance modifiedChart_isOpenImmersion : IsOpenImmersion (modifiedChart p i V) := inferInstance
instance unchangedChart_isOpenImmersion : IsOpenImmersion (unchangedChart p i V) := inferInstance

@[reassoc (attr := simp)] lemma modifiedChart_triangle :
    modifiedChart p i V ≫ map p i V = p ≫ i := inl_gluedMap ..
@[reassoc (attr := simp)] lemma unchangedChart_triangle :
    unchangedChart p i V ≫ map p i V = V.ι := inr_gluedMap ..

lemma charts_cover (z : glued p i V) :
    (∃ y, modifiedChart p i V y = z) ∨ (∃ v, unchangedChart p i V v = z) := openPushout_covered ..

lemma modifiedChart_isPullback :
    IsPullback p (modifiedChart p i V) i (map p i V) :=
  inl_isPullback _ _ _ _ _ _ (range_overlapToUnchanged p i V)
lemma unchangedChart_isPullback :
    IsPullback (𝟙 V.toScheme) (unchangedChart p i V) V.ι (map p i V) :=
  inr_isPullback _ _ _ _ _ _ (range_overlapToModified p i V)

lemma map_isProper [IsProper p] (hcover : i.opensRange ⊔ V = ⊤) :
    IsProper (map p i V) := by
  apply isProper_gluedMap
  · exact range_overlapToModified p i V
  · exact range_overlapToUnchanged p i V
  · simpa using hcover

instance map_restrict_V_isIso : IsIso (map p i V ∣_ V) := by
  have hp : IsIso (pullback.snd (map p i V) V.ι) := by
    rw [← isIso_comp_left_iff (unchangedChart_isPullback p i V).flip.isoPullback.hom]
    simpa using (inferInstance : IsIso (𝟙 V.toScheme))
  have h := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange (map p i V) V.ι)).mpr hp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictEq (map p i V) (Scheme.Opens.opensRange_ι V))).mp h
end OfRestriction

/-- Ordinary local modification data. The overlap identification is an actual
isomorphism equal to the restricted modification map. No resolution, blowup,
or global-gluing existence statement is assumed. -/
structure Datum {X : Scheme.{u}} (U V : X.Opens) where
  Y : Scheme.{u}
  map : Y ⟶ U
  proper : IsProper map
  overlapIso : (map ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).toScheme ≅ (U.ι ⁻¹ᵁ V).toScheme
  overlapIso_hom : overlapIso.hom = map ∣_ (U.ι ⁻¹ᵁ V)

attribute [instance] Datum.proper

namespace Datum
variable {X : Scheme.{u}} {U V : X.Opens} (D : Datum U V)

abbrev overlap : Scheme.{u} := (D.map ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).toScheme
abbrev overlapToModified : D.overlap ⟶ D.Y := (D.map ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι

def overlapToUnchanged : D.overlap ⟶ V := D.overlapIso.hom ≫ (U.ι ∣_ V)

instance overlapToUnchanged_isOpenImmersion : IsOpenImmersion D.overlapToUnchanged := by
  dsimp [overlapToUnchanged]
  infer_instance

lemma overlap_triangle : D.overlapToModified ≫ (D.map ≫ U.ι) =
    D.overlapToUnchanged ≫ V.ι := by
  simp only [overlapToUnchanged, D.overlapIso_hom, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc]

lemma range_overlapToModified : Set.range D.overlapToModified =
    (D.map ≫ U.ι) ⁻¹' Set.range V.ι := by
  simp only [overlapToModified, Scheme.Opens.range_ι]
  rfl

lemma range_overlapToUnchanged : Set.range D.overlapToUnchanged =
    V.ι ⁻¹' Set.range U.ι := by
  change Set.range ((U.ι ∣_ V) ∘ D.overlapIso.hom) = _
  have hs : Function.Surjective D.overlapIso.hom := D.overlapIso.hom.homeomorph.surjective
  rw [hs.range_comp]
  unfold morphismRestrict
  change Set.range ((pullback.snd U.ι V.ι) ∘
    (pullbackRestrictIsoRestrict U.ι V).inv) = _
  have hs : Function.Surjective (pullbackRestrictIsoRestrict U.ι V).inv :=
    (pullbackRestrictIsoRestrict U.ι V).inv.homeomorph.surjective
  rw [hs.range_comp]
  exact IsOpenImmersion.range_pullbackSnd U.ι V.ι

/-- The actual glued scheme, constructed using mathlib's open-immersion pushout. -/
abbrev glued : Scheme.{u} := pushout D.overlapToModified D.overlapToUnchanged

def toBase : D.glued ⟶ X := gluedMap D.overlapToModified D.overlapToUnchanged
  D.map U.ι V.ι D.overlap_triangle

abbrev modifiedChart : D.Y ⟶ D.glued := pushout.inl D.overlapToModified D.overlapToUnchanged
abbrev unchangedChart : V.toScheme ⟶ D.glued :=
  pushout.inr D.overlapToModified D.overlapToUnchanged

instance modifiedChart_isOpenImmersion : IsOpenImmersion D.modifiedChart := inferInstance
instance unchangedChart_isOpenImmersion : IsOpenImmersion D.unchangedChart := inferInstance

@[reassoc (attr := simp)] lemma modifiedChart_triangle :
    D.modifiedChart ≫ D.toBase = D.map ≫ U.ι := inl_gluedMap ..
@[reassoc (attr := simp)] lemma unchangedChart_triangle :
    D.unchangedChart ≫ D.toBase = V.ι := inr_gluedMap ..

lemma charts_cover (z : D.glued) :
    (∃ y, D.modifiedChart y = z) ∨ (∃ v, D.unchangedChart v = z) := openPushout_covered ..

lemma modifiedChart_isPullback : IsPullback D.map D.modifiedChart U.ι D.toBase :=
  inl_isPullback _ _ _ _ _ _ D.range_overlapToUnchanged
lemma unchangedChart_isPullback : IsPullback (𝟙 V.toScheme) D.unchangedChart V.ι D.toBase :=
  inr_isPullback _ _ _ _ _ _ D.range_overlapToModified

lemma toBase_isProper (hcover : U ⊔ V = ⊤) : IsProper D.toBase := by
  apply isProper_gluedMap
  · exact D.range_overlapToModified
  · exact D.range_overlapToUnchanged
  · simpa using hcover

/-- The glued modification is canonically unchanged on the complementary open. -/
instance toBase_restrict_V_isIso : IsIso (D.toBase ∣_ V) := by
  have hp : IsIso (pullback.snd D.toBase V.ι) := by
    rw [← isIso_comp_left_iff D.unchangedChart_isPullback.flip.isoPullback.hom]
    simpa using (inferInstance : IsIso (𝟙 V.toScheme))
  have h := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange D.toBase V.ι)).mpr hp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictEq D.toBase (Scheme.Opens.opensRange_ι V))).mp h
end Datum
end AlgebraicGeometry.Scheme.OpenPushout.Modification

end
end AlgebraicGeometry.Scheme.OpenPushout.Modification
