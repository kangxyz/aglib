/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenReplacement
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Aglib.RingTheory.RegularLocalRing.Domain

/-!
# Gluing an actual local contraction over the original base

The replacement is the published native open pushout. The local map is
given over an actual base open; the other chart is the original complement.
The structure map, its original-source triangle, both base restrictions,
and target-local properness are constructed with their literal maps.

No projective presentation or contraction-existence theorem is assumed for
the original global source. The hypotheses here are the actual local map,
the actual overlap, and the stated covering and inverse-image equations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.ProperGluing

section Overlap

variable {X T : Scheme.{u}}

private theorem overlap_opensRange (U W : X.Opens) :
    (W.ι ∣_ U).opensRange = U.ι ⁻¹ᵁ W := by
  simpa only [Opens.opensRange_ι] using
    Hom.opensRange_of_isPullback (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι U.ι W.ι
      (isPullback_morphismRestrict W.ι U)

/-- The actual overlap is the specified local source complement. -/
private def overlapSourceIso (U W : X.Opens) (Wlocal : U.toScheme.Opens)
    (hW : U.ι ⁻¹ᵁ W = Wlocal) : (W.ι ⁻¹ᵁ U).toScheme ≅ Wlocal.toScheme :=
  IsOpenImmersion.isoOfRangeEq (W.ι ∣_ U) Wlocal.ι (by
    have h := (overlap_opensRange U W).trans hW
    simpa only [Hom.coe_opensRange, Opens.range_ι] using
      congrArg (fun O : U.toScheme.Opens => (O : Set U.toScheme)) h)

@[reassoc]
private theorem overlapSourceIso_hom_ι (U W : X.Opens) (Wlocal : U.toScheme.Opens)
    (hW : U.ι ⁻¹ᵁ W = Wlocal) :
    (overlapSourceIso U W Wlocal hW).hom ≫ Wlocal.ι = W.ι ∣_ U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem overlap_factor (U W : X.Opens) (c : U.toScheme ⟶ T)
    (Wlocal : U.toScheme.Opens) (C : T.Opens) (hW : U.ι ⁻¹ᵁ W = Wlocal)
    (ε : Wlocal.toScheme ≅ C.toScheme) (hε : ε.hom ≫ C.ι = Wlocal.ι ≫ c) :
    (W.ι ∣_ U) ≫ c = (overlapSourceIso U W Wlocal hW ≪≫ ε).hom ≫ C.ι := by
  simp only [Iso.trans_hom, Category.assoc, hε]
  rw [← Category.assoc, overlapSourceIso_hom_ι]

/-- The actual local complement isomorphism makes the native overlap
composite an open immersion. -/
theorem overlap_isOpenImmersion_of_complement (U W : X.Opens) (c : U.toScheme ⟶ T)
    (Wlocal : U.toScheme.Opens) (C : T.Opens) (hW : U.ι ⁻¹ᵁ W = Wlocal)
    (ε : Wlocal.toScheme ≅ C.toScheme) (hε : ε.hom ≫ C.ι = Wlocal.ι ≫ c) :
    IsOpenImmersion ((W.ι ∣_ U) ≫ c) := by
  rw [overlap_factor U W c Wlocal C hW ε hε]
  infer_instance

/-- The overlap has exactly the supplied local target complement as its
range, with the actual source-complement isomorphism retained. -/
theorem overlap_range_of_complement (U W : X.Opens) (c : U.toScheme ⟶ T)
    (Wlocal : U.toScheme.Opens) (C : T.Opens) (hW : U.ι ⁻¹ᵁ W = Wlocal)
    (ε : Wlocal.toScheme ≅ C.toScheme) (hε : ε.hom ≫ C.ι = Wlocal.ι ≫ c) :
    Set.range ((W.ι ∣_ U) ≫ c) = (C : Set T) := by
  rw [overlap_factor U W c Wlocal C hW ε hε]
  rw [← Hom.coe_opensRange, Hom.opensRange_comp_of_isIso, Opens.opensRange_ι]

/-- The local exact inverse-image equation supplies the cartesian overlap
required by the open replacement, without any global contraction premise. -/
theorem overlap_isPullback_of_complement (U W : X.Opens) (c : U.toScheme ⟶ T)
    [IsOpenImmersion ((W.ι ∣_ U) ≫ c)]
    (Wlocal : U.toScheme.Opens) (C : T.Opens) (hW : U.ι ⁻¹ᵁ W = Wlocal)
    (ε : Wlocal.toScheme ≅ C.toScheme) (hε : ε.hom ≫ C.ι = Wlocal.ι ≫ c)
    (hpre : c ⁻¹ᵁ C = Wlocal) :
    IsPullback (𝟙 (W.ι ⁻¹ᵁ U).toScheme) (W.ι ∣_ U) ((W.ι ∣_ U) ≫ c) c := by
  have hRange : ((W.ι ∣_ U) ≫ c).opensRange = C := by
    apply Opens.ext
    simpa only [Hom.coe_opensRange] using
      overlap_range_of_complement U W c Wlocal C hW ε hε
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  rw [hRange, hpre, overlap_opensRange, hW]

end Overlap

variable {X S T : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (W : X.Opens)
  (c : (f ⁻¹ᵁ V).toScheme ⟶ T)
  [IsOpenImmersion ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)]

/-- The target replacing the specified original inverse-image open. -/
abbrev obj : Scheme.{u} := OpenReplacement.OfOpens.target (f ⁻¹ᵁ V) W c

/-- The actual replacement chart. -/
abbrev leftι : T ⟶ obj f V W c :=
  pushout.inl ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι

/-- The unchanged original open chart. -/
abbrev rightι : W.toScheme ⟶ obj f V W c :=
  pushout.inr ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι

/-- The contraction map has the original scheme as its literal source. -/
abbrev contraction (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) : X ⟶ obj f V W c :=
  OpenReplacement.OfOpens.map (f ⁻¹ᵁ V) W hcover c

@[reassoc]
theorem left_contraction (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) :
    (f ⁻¹ᵁ V).ι ≫ contraction f V W c hcover = c ≫ leftι f V W c :=
  OpenReplacement.OfOpens.left_map (f ⁻¹ᵁ V) W hcover c

@[reassoc]
theorem right_contraction (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) :
    W.ι ≫ contraction f V W c hcover = rightι f V W c :=
  OpenReplacement.OfOpens.right_map (f ⁻¹ᵁ V) W hcover c

/-- Surjectivity is proved on the two actual target charts. -/
theorem contraction_surjective [Surjective c] (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) :
    Surjective (contraction f V W c hcover) := by
  constructor
  intro y
  rcases openPushout_covered ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
      (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι y with ⟨t, rfl⟩ | ⟨w, rfl⟩
  · obtain ⟨x, hx⟩ := c.surjective t
    refine ⟨(f ⁻¹ᵁ V).ι x, ?_⟩
    have h : contraction f V W c hcover ((f ⁻¹ᵁ V).ι x) =
        leftι f V W c (c x) :=
      congrArg (fun g : (f ⁻¹ᵁ V).toScheme ⟶ obj f V W c => g x)
        (left_contraction f V W c hcover)
    exact h.trans (congrArg (leftι f V W c) hx)
  · exact ⟨W.ι w, congrArg (fun g : W.toScheme ⟶ obj f V W c => g w)
      (right_contraction f V W c hcover)⟩

/-- The exact local overlap condition makes the original-source map proper. -/
theorem contraction_isProper [IsProper c] (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    (Hoverlap : IsPullback (𝟙 (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme)
      (W.ι ∣_ (f ⁻¹ᵁ V)) ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) c) :
    IsProper (contraction f V W c hcover) :=
  OpenReplacement.OfOpens.isProper_map (f ⁻¹ᵁ V) W hcover c Hoverlap

/-- The restriction over the unchanged target chart is the original isomorphism. -/
theorem contraction_isIso_restrict (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    (Hoverlap : IsPullback (𝟙 (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme)
      (W.ι ∣_ (f ⁻¹ᵁ V)) ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) c) :
    IsIso (contraction f V W c hcover ∣_ (rightι f V W c).opensRange) :=
  OpenReplacement.OfOpens.isIso_restrict_unchanged (f ⁻¹ᵁ V) W hcover c Hoverlap

/-- Noetherianity uses the finite open cover, not descent along a proper map. -/
theorem isNoetherian_obj [IsNoetherian X] [IsNoetherian T] : IsNoetherian (obj f V W c) := by
  let C := OpenNormalizationGluing.twoChartCover
    ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
  let : Finite C.I₀ := by
    change Finite Bool
    infer_instance
  let : IsLocallyNoetherian (obj f V W c) :=
    OpenReplacement.OfOpens.isLocallyNoetherian_target (f ⁻¹ᵁ V) W c
  let : ∀ i, CompactSpace (C.X i) := by
    intro i
    cases i
    · change CompactSpace T
      infer_instance
    · change CompactSpace W.toScheme
      exact isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (W : Set X))
  let : CompactSpace (obj f V W c) := Scheme.OpenCover.compactSpace C
  exact ⟨⟩

/-- Regularity is inherited from the actual replacement and original complement. -/
theorem regularStalks_obj (hX : RegularStalks X) (hT : RegularStalks T) :
    RegularStalks (obj f V W c) :=
  OpenReplacement.OfOpens.regularStalks_target (f ⁻¹ᵁ V) W c hT
    (hX.of_isOpenImmersion W.ι)

/-- The surjective original-source map gives irreducibility; the actual regular
stalks give reducedness. Together they give integrality of the constructed target. -/
theorem isIntegral_obj [IsIntegral X] [Surjective c]
    (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) (hX : RegularStalks X) (hT : RegularStalks T) :
    IsIntegral (obj f V W c) := by
  have hreg := regularStalks_obj f V W c hX hT
  let : ∀ y : obj f V W c, _root_.IsReduced ((obj f V W c).presheaf.stalk y) := by
    intro y
    let : IsRegularLocalRing ((obj f V W c).presheaf.stalk y) := hreg y
    let : IsDomain ((obj f V W c).presheaf.stalk y) :=
      IsRegularLocalRing.isDomain_of_regularLocal _
    infer_instance
  let : IsReduced (obj f V W c) := isReduced_of_isReduced_stalk _
  let : IrreducibleSpace (obj f V W c) :=
    Function.Surjective.irreducibleSpace (contraction f V W c hcover).continuous
      (contraction_surjective f V W c hcover).surj
  exact isIntegral_of_irreducibleSpace_of_isReduced _

section StructureMap

variable (q : T ⟶ V.toScheme) (hc : c ≫ q = f ∣_ V)

/-- The actual structure map glues the local base map to the original map
on the unchanged complement. -/
def structureMap : obj f V W c ⟶ S :=
  pushout.desc (q ≫ V.ι) (W.ι ≫ f) (by
    calc
      ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) ≫ (q ≫ V.ι) =
          (W.ι ∣_ (f ⁻¹ᵁ V)) ≫ ((c ≫ q) ≫ V.ι) := by simp only [Category.assoc]
      _ = (W.ι ∣_ (f ⁻¹ᵁ V)) ≫ ((f ∣_ V) ≫ V.ι) := by rw [hc]
      _ = (W.ι ∣_ (f ⁻¹ᵁ V)) ≫ ((f ⁻¹ᵁ V).ι ≫ f) := by
        rw [morphismRestrict_ι]
      _ = (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ (W.ι ≫ f) := by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc])

@[reassoc (attr := simp)]
theorem left_structureMap :
    leftι f V W c ≫ structureMap f V W c q hc = q ≫ V.ι := by
  simp only [leftι, structureMap, pushout.inl_desc]

@[reassoc (attr := simp)]
theorem right_structureMap :
    rightι f V W c ≫ structureMap f V W c q hc = W.ι ≫ f := by
  simp only [rightι, structureMap, pushout.inr_desc]

/-- The glued map retains the original structural triangle. -/
@[reassoc (attr := simp)]
theorem contraction_structureMap (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) :
    contraction f V W c hcover ≫ structureMap f V W c q hc = f := by
  apply (Scheme.isPushout_opens_of_sup_eq_top (f ⁻¹ᵁ V) W hcover).hom_ext
  · rw [← Category.assoc, left_contraction, Category.assoc, left_structureMap,
      ← Category.assoc c q V.ι, hc, morphismRestrict_ι]
  · rw [← Category.assoc, right_contraction, right_structureMap]

/-- The inverse image of the original base open is exactly the replacement chart. -/
theorem structureMap_preimage :
    structureMap f V W c q hc ⁻¹ᵁ V = (leftι f V W c).opensRange := by
  ext y
  change structureMap f V W c q hc y ∈ V ↔ ∃ t, leftι f V W c t = y
  constructor
  · intro hy
    rcases openPushout_covered ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
        (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι y with ⟨t, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨t, rfl⟩
    · have hw : f (W.ι w) ∈ V := by
        have h : structureMap f V W c q hc (rightι f V W c w) = f (W.ι w) :=
          congrArg (fun g : W.toScheme ⟶ S => g w) (right_structureMap f V W c q hc)
        rwa [h] at hy
      let z : (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme := ⟨w, hw⟩
      refine ⟨c ((W.ι ∣_ (f ⁻¹ᵁ V)) z), ?_⟩
      exact congrArg (fun g : (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ obj f V W c => g z)
        (pushout.condition (f := (W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
          (g := (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι))
  · rintro ⟨t, rfl⟩
    have h : structureMap f V W c q hc (leftι f V W c t) = V.ι (q t) :=
      congrArg (fun g : T ⟶ S => g t) (left_structureMap f V W c q hc)
    rw [h]
    exact (q t).property

/-- The actual replacement chart is cartesian over the original base open. -/
theorem structureMap_isPullback_left :
    IsPullback q (leftι f V W c) V.ι (structureMap f V W c q hc) :=
  IsOpenImmersion.isPullback _ _ _ _ (left_structureMap f V W c q hc)
    (by simpa only [Opens.opensRange_ι] using structureMap_preimage f V W c q hc)

/-- The inverse image of the original base open is canonically the given local target. -/
def replacementIso : T ≅ (structureMap f V W c q hc ⁻¹ᵁ V).toScheme :=
  (structureMap_isPullback_left f V W c q hc).flip.isoPullback ≪≫
    pullbackRestrictIsoRestrict (structureMap f V W c q hc) V

@[reassoc (attr := simp)]
theorem replacementIso_hom_structure :
    (replacementIso f V W c q hc).hom ≫ (structureMap f V W c q hc ∣_ V) = q := by
  simp only [replacementIso, Iso.trans_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict, IsPullback.isoPullback_hom_snd]

variable (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)

/-- The original map from an unchanged inverse-image base open to the glued target. -/
def awayMap (Z : S.Opens) : (f ⁻¹ᵁ Z).toScheme ⟶ obj f V W c :=
  (f ⁻¹ᵁ Z).ι ≫ contraction f V W c hcover

/-- If this original base restriction lies in the unchanged complement,
its map is literally an open-chart inclusion after the original open inclusion. -/
theorem awayMap_eq (Z : S.Opens) (hZ : f ⁻¹ᵁ Z ≤ W) :
    awayMap f V W c hcover Z = X.homOfLE hZ ≫ rightι f V W c := by
  rw [← right_contraction f V W c hcover, ← Category.assoc, Scheme.homOfLE_ι]
  rfl

/-- The original map over such a base open is an open immersion. -/
theorem awayMap_isOpenImmersion (Z : S.Opens) (hZ : f ⁻¹ᵁ Z ≤ W) :
    IsOpenImmersion (awayMap f V W c hcover Z) := by
  rw [awayMap_eq f V W c hcover Z hZ]
  infer_instance

/-- Surjectivity and the structural triangle identify the range over an
arbitrary base open using the original source points. -/
theorem structureMap_preimage_away [Surjective c] (Z : S.Opens) :
    (structureMap f V W c q hc ⁻¹ᵁ Z : Set (obj f V W c)) =
      Set.range (awayMap f V W c hcover Z) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (contraction_surjective f V W c hcover).surj y
    have hxZ : f x ∈ Z := by
      have h : structureMap f V W c q hc (contraction f V W c hcover x) = f x :=
        congrArg (fun g : X ⟶ S => g x) (contraction_structureMap f V W c q hc hcover)
      rw [← h, hx]
      exact hy
    exact ⟨⟨x, hxZ⟩, hx⟩
  · rintro ⟨x, rfl⟩
    have h : structureMap f V W c q hc
        (contraction f V W c hcover ((f ⁻¹ᵁ Z).ι x)) = f ((f ⁻¹ᵁ Z).ι x) :=
      congrArg (fun g : X ⟶ S => g ((f ⁻¹ᵁ Z).ι x))
        (contraction_structureMap f V W c q hc hcover)
    change structureMap f V W c q hc
      (contraction f V W c hcover ((f ⁻¹ᵁ Z).ι x)) ∈ Z
    rw [h]
    exact x.property

/-- Over a base open avoiding the exceptional source, the actual structural
square is the original restriction of `f`. -/
theorem structureMap_isPullback_away [Surjective c]
    (Z : S.Opens) (hZ : f ⁻¹ᵁ Z ≤ W) :
    IsPullback (f ∣_ Z) (awayMap f V W c hcover Z) Z.ι (structureMap f V W c q hc) := by
  let : IsOpenImmersion (awayMap f V W c hcover Z) :=
    awayMap_isOpenImmersion f V W c hcover Z hZ
  apply IsOpenImmersion.isPullback
  · rw [awayMap, Category.assoc, contraction_structureMap, morphismRestrict_ι]
  · apply Opens.ext
    simpa only [Opens.opensRange_ι, Hom.coe_opensRange] using
      structureMap_preimage_away f V W c q hc hcover Z

/-- The unchanged base restriction is identified with the original one as a scheme. -/
def awayIso [Surjective c] (Z : S.Opens) (hZ : f ⁻¹ᵁ Z ≤ W) :
    (f ⁻¹ᵁ Z).toScheme ≅ (structureMap f V W c q hc ⁻¹ᵁ Z).toScheme :=
  (structureMap_isPullback_away f V W c q hc hcover Z hZ).flip.isoPullback ≪≫
    pullbackRestrictIsoRestrict (structureMap f V W c q hc) Z

@[reassoc (attr := simp)]
theorem awayIso_hom_structure [Surjective c] (Z : S.Opens) (hZ : f ⁻¹ᵁ Z ≤ W) :
    (awayIso f V W c q hc hcover Z hZ).hom ≫
      (structureMap f V W c q hc ∣_ Z) = f ∣_ Z := by
  simp only [awayIso, Iso.trans_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict, IsPullback.isoPullback_hom_snd]

/-- Properness of the glued structure map follows on the two stated base
opens. The unchanged piece uses the original proper map, not properness of
an arbitrary source-open restriction. -/
theorem structureMap_isProper [Surjective c] [IsProper f] [IsProper q]
    (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    (Z : S.Opens) (hbase : V ⊔ Z = ⊤) (hZ : f ⁻¹ᵁ Z ≤ W) :
    IsProper (structureMap f V W c q hc) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper)
    (OpenUnionPushout.cover V.ι Z.ι (by simpa only [Opens.opensRange_ι] using hbase))
  intro i
  cases i
  · change IsProper (pullback.snd (structureMap f V W c q hc) V.ι)
    rw [← (structureMap_isPullback_left f V W c q hc).flip.isoPullback_inv_snd]
    infer_instance
  · change IsProper (pullback.snd (structureMap f V W c q hc) Z.ι)
    rw [← (structureMap_isPullback_away f V W c q hc hcover Z hZ).flip.isoPullback_inv_snd]
    infer_instance

end StructureMap

section Point

variable {k : Type u} [Field k] (ρ : Spec (.of k) ⟶ T)

/-- The original full field point, followed by the actual replacement chart. -/
def point : Spec (.of k) ⟶ obj f V W c := ρ ≫ leftι f V W c

/-- A full closed field point disjoint from the local overlap stays closed
in the actual glued scheme. -/
theorem point_isClosedImmersion [IsClosedImmersion ρ]
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ) :
    IsClosedImmersion (point f V W c ρ) := by
  apply OpenReplacement.isClosedImmersion_inl_of_disjoint
  refine Set.disjoint_left.mpr ?_
  intro t ht hto
  rw [hcompl] at hto
  exact hto ht

/-- The unchanged chart is exactly the complement of the original full
field point in the glued target. -/
theorem range_right_eq_compl_point
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ) :
    Set.range (rightι f V W c) = (Set.range (point f V W c ρ))ᶜ := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩ ⟨z, hz⟩
    have he : leftι f V W c (ρ z) = rightι f V W c w := hz
    obtain ⟨a, ha, -⟩ :=
      (OpenNormalizationGluing.left_eq_right_iff
        ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι (ρ z) w).mp he
    have hmem : ρ z ∈ Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) := ⟨a, ha⟩
    rw [hcompl] at hmem
    exact hmem ⟨z, rfl⟩
  · intro hy
    rcases openPushout_covered ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
        (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι y with ⟨t, rfl⟩ | ⟨w, rfl⟩
    · have ht : t ∉ Set.range ρ := by
        rintro ⟨z, rfl⟩
        exact hy ⟨z, rfl⟩
      have hmem : t ∈ Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) := by
        rw [hcompl]
        exact ht
      obtain ⟨a, ha⟩ := hmem
      refine ⟨(W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι a, ?_⟩
      have h := congrArg (fun g : (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ obj f V W c => g a)
        (pushout.condition (f := (W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
          (g := (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι))
      exact h.symm.trans (congrArg (leftι f V W c) ha)
    · exact ⟨w, rfl⟩

/-- The complement isomorphism uses the original unchanged chart. -/
def complementIso : W.toScheme ≅ (rightι f V W c).opensRange.toScheme :=
  (rightι f V W c).isoOpensRange

@[reassoc (attr := simp)]
theorem complementIso_hom (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤) :
    (complementIso f V W c).hom ≫ (rightι f V W c).opensRange.ι =
      W.ι ≫ contraction f V W c hcover := by
  simp only [complementIso, Scheme.Hom.isoOpensRange_hom_ι, right_contraction]

/-- The original full point ideal is recovered on the replacement chart. -/
theorem pointIdeal_comap_left [IsNoetherian T] :
    (point f V W c ρ).ker.comap (leftι f V W c) = ρ.ker := by
  rw [point, Hom.ker_comp]
  exact ρ.ker.comap_map_of_isOpenImmersion (leftι f V W c)

/-- The actual point ideal is the unit ideal on the unchanged chart. -/
theorem pointIdeal_comap_right [IsClosedImmersion ρ]
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ) :
    (point f V W c ρ).ker.comap (rightι f V W c) = ⊤ := by
  let : IsClosedImmersion (point f V W c ρ) :=
    point_isClosedImmersion f V W c ρ hcompl
  apply (IdealSheafData.range_subset_compl_support_iff _ _).mp
  intro y hy
  change y ∉ ((point f V W c ρ).ker.support : Set (obj f V W c))
  rw [Hom.support_ker, (point f V W c ρ).isClosedEmbedding.isClosed_range.closure_eq]
  rw [range_right_eq_compl_point f V W c ρ hcompl] at hy
  exact hy

/-- The original local full-field-point fibre square pastes with the actual
replacement-chart square, retaining the original exceptional scheme. -/
theorem point_isPullback (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    {D : Scheme.{u}} (i : D ⟶ X) (iU : D ⟶ (f ⁻¹ᵁ V).toScheme)
    (a : D ⟶ Spec (.of k)) [IsClosedImmersion iU] [IsClosedImmersion ρ]
    (hi : iU ≫ (f ⁻¹ᵁ V).ι = i) (htri : iU ≫ c = a ≫ ρ)
    (hker : ρ.ker.comap c = iU.ker) :
    IsPullback i a (contraction f V W c hcover) (point f V W c ρ) := by
  have Hlocal := isPullback_of_isClosedImmersion iU ρ a c htri hker
  have H := Hlocal.flip.paste_vert
    (OpenReplacement.OfOpens.isPullback_left (f ⁻¹ᵁ V) W hcover c)
  simpa only [hi, point] using H.flip

/-- The full original exceptional ideal is the pullback of the full global
field-point ideal, not merely an equality of their supports. -/
theorem pointIdeal_comap_contraction (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    {D : Scheme.{u}} (i : D ⟶ X) (iU : D ⟶ (f ⁻¹ᵁ V).toScheme)
    (a : D ⟶ Spec (.of k)) [IsClosedImmersion iU] [IsClosedImmersion ρ]
    (hi : iU ≫ (f ⁻¹ᵁ V).ι = i) (htri : iU ≫ c = a ≫ ρ)
    (hker : ρ.ker.comap c = iU.ker)
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ) :
    (point f V W c ρ).ker.comap (contraction f V W c hcover) = i.ker := by
  let : IsClosedImmersion (point f V W c ρ) :=
    point_isClosedImmersion f V W c ρ hcompl
  let H := point_isPullback f V W c ρ hcover i iU a hi htri hker
  calc
    (point f V W c ρ).ker.comap (contraction f V W c hcover) =
        (pullback.fst (contraction f V W c hcover) (point f V W c ρ)).ker :=
      (IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = (H.isoPullback.hom ≫
        pullback.fst (contraction f V W c hcover) (point f V W c ρ)).ker :=
      (Hom.ker_comp_of_isIso _ _).symm
    _ = i.ker := by rw [H.isoPullback_hom_fst]

/-- The global point ideal has the original Cartier pullback. The ideal
module comparison uses the actual image isomorphism of the original immersion. -/
theorem pointIdeal_cartierPullback (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    {D : Scheme.{u}} (i : D ⟶ X) (iU : D ⟶ (f ⁻¹ᵁ V).toScheme)
    (a : D ⟶ Spec (.of k)) [IsClosedImmersion i] [IsClosedImmersion iU]
    [IsClosedImmersion ρ] (hi : iU ≫ (f ⁻¹ᵁ V).ι = i)
    (htri : iU ≫ c = a ≫ ρ) (hker : ρ.ker.comap c = iU.ker)
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ)
    (hI : Modules.Invertible.IsLocallyRankOne X (Hom.idealModule i)) :
    Blowup.cartierPullback (point f V W c ρ).ker (contraction f V W c hcover) := by
  unfold Blowup.cartierPullback
  rw [pointIdeal_comap_contraction f V W c ρ hcover i iU a hi htri hker hcompl]
  let e := Blowup.RegularPoint.closedImmersionImageIso i
  have he : e.inv ≫ i = i.ker.subschemeι := by
    calc
      e.inv ≫ i = e.inv ≫ (e.hom ≫ i.ker.subschemeι) :=
        congrArg (fun g => e.inv ≫ g)
          (Blowup.RegularPoint.closedImmersionImageIso_hom_ι i).symm
      _ = i.ker.subschemeι := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact Modules.Invertible.isLocallyRankOne_of_iso X
    (Blowup.RegularPoint.identityBaseIdealIso i i.ker.subschemeι e.symm he) hI

end Point

section BlowupComparison

/-- The original canonical lift commutes with a specified open base chart.
Cartesian cancellation identifies its actual restriction with the local lift. -/
private theorem lift_isPullback_on_open
    {X₀ Y₀ U₀ T₀ : Scheme.{u}} {I : Y₀.IdealSheafData} {J : T₀.IdealSheafData}
    (b : X₀ ⟶ Y₀) (a : U₀ ⟶ X₀) (j : T₀ ⟶ Y₀) [IsOpenImmersion j]
    (d : U₀ ⟶ T₀) (H : IsPullback d a j b)
    (B : Blowup.BlowupDatum I) (C : Blowup.BlowupDatum J)
    (hJ : I.comap j = J) (hb : Blowup.cartierPullback I b)
    (hd : Blowup.cartierPullback J d) :
    IsPullback (C.lift d hd) a (Blowup.BaseChange.map j hJ B C) (B.lift b hb) := by
  have hab : Blowup.cartierPullback I (a ≫ b) := by
    unfold Blowup.cartierPullback
    rw [← H.w, IdealSheafData.comap_comp, hJ]
    exact hd
  have htri : C.lift d hd ≫ Blowup.BaseChange.map j hJ B C = a ≫ B.lift b hb := by
    apply B.hom_ext hab
    · calc
        (C.lift d hd ≫ Blowup.BaseChange.map j hJ B C) ≫ B.map =
            (C.lift d hd ≫ C.map) ≫ j := by
          rw [Category.assoc, Blowup.BaseChange.map_triangle, ← Category.assoc]
        _ = d ≫ j := by rw [C.lift_map]
        _ = a ≫ b := H.w
    · rw [Category.assoc, B.lift_map]
  have Houter : IsPullback (C.lift d hd ≫ C.map) a j (B.lift b hb ≫ B.map) := by
    simpa only [Blowup.BlowupDatum.lift_map] using H
  exact Houter.of_right htri
    (Blowup.BaseChange.isPullback_of_flat j inferInstance hJ B C).flip

/-- The canonical global lift to the blowup of the original full field point
is an isomorphism. The two comparisons are made on actual open charts of that
blowup: the supplied local point blowup and the trivial blowup off the point. -/
theorem contraction_isBlowup [IsNoetherian T]
    {k : Type u} [Field k] (ρ : Spec (.of k) ⟶ T) [IsClosedImmersion ρ]
    (hcover : (f ⁻¹ᵁ V) ⊔ W = ⊤)
    (Hoverlap : IsPullback (𝟙 (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme)
      (W.ι ∣_ (f ⁻¹ᵁ V)) ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) c)
    (hcompl : Set.range ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c) = (Set.range ρ)ᶜ)
    (hf : Blowup.cartierPullback (point f V W c ρ).ker (contraction f V W c hcover))
    (hc : Blowup.cartierPullback ρ.ker c)
    (hlocal : IsIso ((Blowup.blowupDatum ρ.ker).lift c hc)) :
    IsIso ((Blowup.blowupDatum (point f V W c ρ).ker).lift
      (contraction f V W c hcover) hf) := by
  let B := Blowup.blowupDatum (point f V W c ρ).ker
  let Bleft := Blowup.blowupDatum ρ.ker
  let Bright := Blowup.flatPullbackDatum B (rightι f V W c)
  let l := B.lift (contraction f V W c hcover) hf
  have hleft := pointIdeal_comap_left f V W c ρ
  have hright := pointIdeal_comap_right f V W c ρ hcompl
  let aleft := Blowup.BaseChange.map (leftι f V W c) hleft B Bleft
  let aright := Blowup.BaseChange.map (rightι f V W c) rfl B Bright
  have Hleft : IsPullback aleft Bleft.map B.map (leftι f V W c) :=
    Blowup.BaseChange.isPullback_of_flat _ inferInstance hleft B Bleft
  have Hright : IsPullback aright Bright.map B.map (rightι f V W c) :=
    Blowup.BaseChange.isPullback_of_flat _ inferInstance rfl B Bright
  let : IsOpenImmersion aleft := by
    rw [← Hleft.isoPullback_hom_fst]
    infer_instance
  let : IsOpenImmersion aright := by
    rw [← Hright.isoPullback_hom_fst]
    infer_instance
  let : IsIso (Bleft.lift c hc) := hlocal
  have hcright : Blowup.cartierPullback
      ((point f V W c ρ).ker.comap (rightι f V W c)) (𝟙 W.toScheme) :=
    Blowup.cartier_of_comap_eq_top _ _ (by rw [IdealSheafData.comap_id, hright])
  let : IsIso Bright.map := by
    change IsIso (pullback.snd B.map (rightι f V W c))
    exact B.pullback_snd_isIso_of_comap_eq_top _ hright
  let : IsIso (Bright.lift (𝟙 W.toScheme) hcright) := by
    apply (isIso_comp_right_iff _ Bright.map).mp
    rw [Bright.lift_map]
    infer_instance
  have Hl : IsPullback (Bleft.lift c hc) (f ⁻¹ᵁ V).ι aleft l :=
    lift_isPullback_on_open (contraction f V W c hcover) (f ⁻¹ᵁ V).ι
      (leftι f V W c) c
      (OpenReplacement.OfOpens.isPullback_left (f ⁻¹ᵁ V) W hcover c)
      B Bleft hleft hf hc
  have Hr : IsPullback (Bright.lift (𝟙 W.toScheme) hcright) W.ι aright l :=
    lift_isPullback_on_open (contraction f V W c hcover) W.ι
      (rightι f V W c) (𝟙 W.toScheme)
      (OpenReplacement.OfOpens.isPullback_right (f ⁻¹ᵁ V) W hcover c Hoverlap)
      B Bright rfl hf hcright
  have hcharts : aleft.opensRange ⊔ aright.opensRange = ⊤ := by
    rw [Hom.opensRange_of_isPullback aleft Bleft.map B.map (leftι f V W c) Hleft,
      Hom.opensRange_of_isPullback aright Bright.map B.map (rightι f V W c) Hright]
    apply top_unique
    intro z _
    change B.map z ∈ (leftι f V W c).opensRange ∨
      B.map z ∈ (rightι f V W c).opensRange
    rcases openPushout_covered ((W.ι ∣_ (f ⁻¹ᵁ V)) ≫ c)
        (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V)).ι (B.map z) with ⟨t, ht⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr ⟨w, hw⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (OpenUnionPushout.cover aleft aright hcharts)
  intro j
  cases j
  · change IsIso (pullback.snd l aleft)
    rw [← Hl.flip.isoPullback_inv_snd]
    infer_instance
  · change IsIso (pullback.snd l aright)
    rw [← Hr.flip.isoPullback_inv_snd]
    infer_instance

end BlowupComparison

end AlgebraicGeometry.Scheme.Surfaces.Contraction.ProperGluing
