/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Regularity
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Birational
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Birational.NormalLocus
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Recognition of the original regular-local point blowup

A proper modification of a regular local surface whose literal closed fibre
is an integral Cartier curve is its actual point blowup. The comparison is
the existing universal Cartier-ideal lift. Properness and the common dense
open make this map surjective; its literal closed-fibre map is consequently
a proper dominant map of curves and is finite. The original factor is finite
and birational, and regularity of the blowup supplies its normality.

The argument retains the original embedded inverse-image ideal and the actual
residue-field base change. It imposes no coordinate compatibility on the
exceptional curve and no perfectness, excellence or separability assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.BlowupDatum

variable {X W : Scheme.{u}} {I : X.IdealSheafData}
  (B : BlowupDatum I) (f : W ⟶ X) (hf : cartierPullback I f)

/-- The original universal lift is proper when the original map is proper
and the blowdown is separated. -/
theorem lift_isProper [IsProper f] [IsSeparated B.map] : IsProper (B.lift f hf) := by
  have : IsProper (B.lift f hf ≫ B.map) := by
    rw [B.lift_map]
    infer_instance
  exact IsProper.of_comp (B.lift f hf) B.map

/-- The canonical factor is an isomorphism over the actual inverse image of
the centre complement whenever the original map is. -/
theorem lift_restrict_isIso
    [IsIso (f ∣_ centreComplement I)] :
    IsIso (B.lift f hf ∣_ B.map ⁻¹ᵁ centreComplement I) := by
  let : IsIso (B.map ∣_ centreComplement I) :=
    B.restrict_isIso_of_disjoint _ (centreComplement_disjoint I)
  have hcomp : IsIso ((B.lift f hf ≫ B.map) ∣_ centreComplement I) := by
    rw [B.lift_map]
    infer_instance
  rw [morphismRestrict_comp] at hcomp
  exact (isIso_comp_right_iff (B.lift f hf ∣_ B.map ⁻¹ᵁ centreComplement I)
    (B.map ∣_ centreComplement I)).mp hcomp

/-- The factor has dense image because its image contains the original
nonempty open complement in the integral blowup. -/
theorem lift_isDominant [IsIntegral X]
    (hI : genericPoint X ∉ (I.support : Set X))
    [IsIso (f ∣_ centreComplement I)] : IsDominant (B.lift f hf) := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let U := B.map ⁻¹ᵁ centreComplement I
  let : IsIso (B.lift f hf ∣_ U) := B.lift_restrict_isIso f hf
  have hU : (U : Set B.Y).Nonempty := by
    obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support hI
    exact ⟨y, by change B.map y ∉ (I.support : Set X); rwa [hy]⟩
  constructor
  apply (U.isOpen.dense hU).mono
  intro y hy
  obtain ⟨w, hw⟩ := (B.lift f hf ∣_ U).surjective ⟨y, hy⟩
  refine ⟨w.1, ?_⟩
  simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hw

/-- The actual base-change arrow of the universal factor on the original
fibres, preserving both original fibre projections. -/
def liftFibreMap {Z : Scheme.{u}} (c : Z ⟶ X) : pullback f c ⟶ pullback B.map c :=
  pullback.lift (pullback.fst f c ≫ B.lift f hf) (pullback.snd f c) (by
    rw [Category.assoc, B.lift_map]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem liftFibreMap_fst {Z : Scheme.{u}} (c : Z ⟶ X) :
    B.liftFibreMap f hf c ≫ pullback.fst B.map c =
      pullback.fst f c ≫ B.lift f hf :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem liftFibreMap_snd {Z : Scheme.{u}} (c : Z ⟶ X) :
    B.liftFibreMap f hf c ≫ pullback.snd B.map c = pullback.snd f c :=
  pullback.lift_snd _ _ _

/-- The fibre comparison is a literal base change of the original universal
factor, rather than an independently chosen map between the fibres. -/
theorem liftFibreMap_isPullback {Z : Scheme.{u}} (c : Z ⟶ X) :
    IsPullback (B.liftFibreMap f hf c) (pullback.fst f c)
      (pullback.fst B.map c) (B.lift f hf) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd B.map c) (h₂₂ := B.map)
  · rw [B.liftFibreMap_snd, B.lift_map]
    exact (IsPullback.of_hasPullback f c).flip
  · exact B.liftFibreMap_fst f hf c
  · exact (IsPullback.of_hasPullback B.map c).flip

end AlgebraicGeometry.Scheme.Blowup.BlowupDatum

namespace AlgebraicGeometry.Scheme.Blowup

private theorem finite_preimage_singleton_of_finite_closed_baseChange
    {C D W B : Scheme.{u}} (a : C ⟶ D) (i : C ⟶ W) (j : D ⟶ B) (q : W ⟶ B)
    (h : IsPullback a i j q) [IsFinite a] (d : D) :
    (q ⁻¹' {j d}).Finite := by
  have he := Scheme.image_preimage_eq_of_isPullback h ({d} : Set D)
  have hf := (a.finite_preimage_singleton d).image i
  rw [Set.image_singleton] at he
  exact he ▸ hf

/-- A normal integral blowup is recognized by a proper modification with the
same actual centre complement and integral one-dimensional literal fibres.
No compatibility with coordinates or conormal frames is assumed. -/
theorem BlowupDatum.isIso_lift_of_curve_fibre
    {X W Z : Scheme.{u}} [IsIntegral X] [IsIntegral W] [IsNoetherian Z]
    (c : Z ⟶ X) [IsClosedImmersion c] (B : BlowupDatum c.ker)
    [IsSeparated B.map] (f : W ⟶ X) [IsProper f]
    (hf : cartierPullback c.ker f)
    (hI : genericPoint X ∉ (c.ker.support : Set X))
    (hB : NormalStalks B.Y)
    [IsIntegral (pullback f c)] [IsIntegral (pullback B.map c)]
    (hC : topologicalKrullDim (pullback f c : Scheme.{u}) ≤ 1)
    (hD : topologicalKrullDim (pullback B.map c : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement c.ker)] : IsIso (B.lift f hf) := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let q := B.lift f hf
  let U := B.map ⁻¹ᵁ centreComplement c.ker
  let a := B.liftFibreMap f hf c
  let j := pullback.fst B.map c
  let : IsProper q := B.lift_isProper f hf
  let : IsDominant q := B.lift_isDominant f hf hI
  let : Surjective q := inferInstance
  let : IsIso (q ∣_ U) := B.lift_restrict_isIso f hf
  let : IsProper a := MorphismProperty.of_isPullback
    (P := @IsProper) (B.liftFibreMap_isPullback f hf c).flip inferInstance
  let : Surjective a := MorphismProperty.of_isPullback
    (P := @Surjective) (B.liftFibreMap_isPullback f hf c).flip inferInstance
  let : IsLocallyNoetherian (pullback f c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f c)
  let : CompactSpace (pullback f c : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f c)
  let : IsNoetherian (pullback f c) := ⟨⟩
  let : IsFinite a :=
    Scheme.OverField.Curve.Projectivity.proper_dominant_curve_isFinite a hC hD
  have hfinite (y : B.Y) : (q ⁻¹' {y}).Finite := by
    by_cases hy : y ∈ Set.range j
    · obtain ⟨d, rfl⟩ := hy
      exact finite_preimage_singleton_of_finite_closed_baseChange a
        (pullback.fst f c) j q (B.liftFibreMap_isPullback f hf c) d
    · have hyU : y ∈ U := by
        change B.map y ∉ (c.ker.support : Set X)
        rw [Hom.support_ker, c.isClosedEmbedding.isClosed_range.closure_eq]
        simpa only [j, Scheme.Pullback.range_fst, Set.mem_preimage] using hy
      apply Set.Subsingleton.finite
      intro w hw v hv
      change q w = y at hw
      change q v = y at hv
      have hwU : w ∈ q ⁻¹ᵁ U := by change q w ∈ U; rwa [hw]
      have hvU : v ∈ q ⁻¹ᵁ U := by change q v ∈ U; rwa [hv]
      have he : (q ∣_ U) ⟨w, hwU⟩ = (q ∣_ U) ⟨v, hvU⟩ := by
        apply Subtype.ext
        exact (morphismRestrict_base_coe q U ⟨w, hwU⟩).trans
          ((hw.trans hv.symm).trans (morphismRestrict_base_coe q U ⟨v, hvU⟩).symm)
      exact congrArg Subtype.val ((q ∣_ U).isOpenEmbedding.injective he)
  let : LocallyQuasiFinite q := LocallyQuasiFinite.of_finite_preimage_singleton q hfinite
  let : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  let : Nonempty U := by
    obtain ⟨y, hy⟩ := B.mem_range_of_not_mem_support hI
    exact ⟨⟨y, by change B.map y ∉ (c.ker.support : Set X); rwa [hy]⟩⟩
  exact Scheme.isIso_of_isFinite_of_isIso_restrict q hB U

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open IsLocalRing Scheme.ProjectiveLine.TwoChart

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

private theorem genericPoint_not_mem_maximalCentre (hd : ringKrullDim A = 2) :
    letI : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
    genericPoint (Spec (.of A)) ∉
      ((affineCenter A (maximalIdeal A)).support : Set (Spec (.of A))) := by
  let : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
  change genericPoint (Spec (.of A)) ∉ ((LocalRing.residueSpecMap A).ker.support : Set _)
  rw [Hom.support_ker,
    (LocalRing.residueSpecMap A).isClosedEmbedding.isClosed_range.closure_eq]
  rintro ⟨z, hz⟩
  have ha : firstParameter A hd ∈ (genericPoint (Spec (.of A))).asIdeal := by
    rw [← hz]
    change IsLocalRing.residue A (firstParameter A hd) ∈ z.asIdeal
    rw [show IsLocalRing.residue A (firstParameter A hd) = 0 from
      (IsLocalRing.residue_eq_zero_iff _).mpr (parameters_spec A hd).1]
    exact z.asIdeal.zero_mem
  rw [genericPoint_eq_bot_of_affine] at ha
  have ha0 : firstParameter A hd = 0 := ha
  exact zero_ne_one ((parameters_spec A hd).2.2.2.1
    (show firstParameter A hd • (0 : A) = firstParameter A hd • (1 : A) by simp [ha0]))

/-- A proper integral modification of the spectrum of a two-dimensional
regular local ring is its actual point blowup when its original closed fibre
is an integral Cartier curve and it is an isomorphism off the closed point.
The conclusion concerns precisely the existing canonical Cartier-ideal lift. -/
theorem isIso_lift_of_integral_closedFibre
    (hd : ringKrullDim A = 2) {W : Scheme.{u}} [IsIntegral W]
    (f : W ⟶ Spec (.of A)) [IsProper f]
    (hf : cartierPullback (affineCenter A (maximalIdeal A)) f)
    [IsIntegral (pullback f (LocalRing.residueSpecMap A))]
    (hC : topologicalKrullDim
      (pullback f (LocalRing.residueSpecMap A) : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement (affineCenter A (maximalIdeal A)))] :
    IsIso ((blowupDatum (affineCenter A (maximalIdeal A))).lift f hf) := by
  let : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
  let B := blowupDatum (affineCenter A (maximalIdeal A))
  let c := LocalRing.residueSpecMap A
  let : IsIso (f ∣_ centreComplement c.ker) := by
    change IsIso (f ∣_ centreComplement (affineCenter A (maximalIdeal A)))
    infer_instance
  let : IsProper B.map := B.isProper_of_spectrum
  let e : pullback B.map c ≅ twoChartLine (.of (ResidueField A)) :=
    (Over.forget _).mapIso (exceptionalOverIsoProjectiveP1 A hd) ≪≫
      (twoChartLineIsoProjectiveP1 (ResidueField A)).symm
  let : IsIntegral (pullback B.map c) := IsIntegral.of_isIso e.inv
  have hD : topologicalKrullDim (pullback B.map c : Scheme.{u}) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
      (Scheme.OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim (ResidueField A))
  have hB : NormalStalks B.Y := by
    intro y
    let : IsRegularLocalRing (B.Y.presheaf.stalk y) := regularStalks A hd y
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  exact B.isIso_lift_of_curve_fibre c f hf
    (genericPoint_not_mem_maximalCentre A hd) hB hC.le hD

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup

/-- The canonical factor is finite already from the literal curve fibres
and the common centre complement; target normality is not needed here. -/
theorem BlowupDatum.isFinite_lift_of_curve_fibre
    {X W Z : Scheme.{u}} [IsIntegral X] [IsNoetherian Z]
    (c : Z ⟶ X) [IsClosedImmersion c] (B : BlowupDatum c.ker)
    [IsSeparated B.map] (f : W ⟶ X) [IsProper f]
    (hf : cartierPullback c.ker f)
    (hI : genericPoint X ∉ (c.ker.support : Set X))
    [IsIntegral (pullback f c)] [IsIntegral (pullback B.map c)]
    (hC : topologicalKrullDim (pullback f c : Scheme.{u}) ≤ 1)
    (hD : topologicalKrullDim (pullback B.map c : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement c.ker)] : IsFinite (B.lift f hf) := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let q := B.lift f hf
  let U := B.map ⁻¹ᵁ centreComplement c.ker
  let a := B.liftFibreMap f hf c
  let j := pullback.fst B.map c
  let : IsProper q := B.lift_isProper f hf
  let : IsDominant q := B.lift_isDominant f hf hI
  let : Surjective q := inferInstance
  let : IsIso (q ∣_ U) := B.lift_restrict_isIso f hf
  let : IsProper a := MorphismProperty.of_isPullback
    (P := @IsProper) (B.liftFibreMap_isPullback f hf c).flip inferInstance
  let : Surjective a := MorphismProperty.of_isPullback
    (P := @Surjective) (B.liftFibreMap_isPullback f hf c).flip inferInstance
  let : IsLocallyNoetherian (pullback f c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f c)
  let : CompactSpace (pullback f c : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f c)
  let : IsNoetherian (pullback f c) := ⟨⟩
  let : IsFinite a :=
    Scheme.OverField.Curve.Projectivity.proper_dominant_curve_isFinite a hC hD
  have hfinite (y : B.Y) : (q ⁻¹' {y}).Finite := by
    by_cases hy : y ∈ Set.range j
    · obtain ⟨d, rfl⟩ := hy
      exact finite_preimage_singleton_of_finite_closed_baseChange a
        (pullback.fst f c) j q (B.liftFibreMap_isPullback f hf c) d
    · have hyU : y ∈ U := by
        change B.map y ∉ (c.ker.support : Set X)
        rw [Hom.support_ker, c.isClosedEmbedding.isClosed_range.closure_eq]
        simpa only [j, Scheme.Pullback.range_fst, Set.mem_preimage] using hy
      apply Set.Subsingleton.finite
      intro w hw v hv
      change q w = y at hw
      change q v = y at hv
      have hwU : w ∈ q ⁻¹ᵁ U := by change q w ∈ U; rwa [hw]
      have hvU : v ∈ q ⁻¹ᵁ U := by change q v ∈ U; rwa [hv]
      have he : (q ∣_ U) ⟨w, hwU⟩ = (q ∣_ U) ⟨v, hvU⟩ := by
        apply Subtype.ext
        exact (morphismRestrict_base_coe q U ⟨w, hwU⟩).trans
          ((hw.trans hv.symm).trans (morphismRestrict_base_coe q U ⟨v, hvU⟩).symm)
      exact congrArg Subtype.val ((q ∣_ U).isOpenEmbedding.injective he)
  let : LocallyQuasiFinite q := LocallyQuasiFinite.of_finite_preimage_singleton q hfinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite q

end AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open IsLocalRing Scheme.ProjectiveLine.TwoChart

private theorem isClosed_imagePoint {Y : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c] :
    IsClosed ({c (closedPoint K)} : Set Y) := by
  have himage : (fun z : Spec (.of K) => c z) '' {closedPoint K} =
      ({c (closedPoint K)} : Set Y) := Set.image_singleton
  exact himage ▸
    c.isClosedEmbedding.isClosedMap ({closedPoint K} : Set (Spec (.of K))) isClosed_singleton

/-- The canonical residue factor of the original closed field point is an
isomorphism, with no chosen identification of its field. -/
private theorem isIso_closedPointResidueFactor {Y : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c] :
    IsIso (Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo c))) := by
  let i := Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo c))
  let c₀ := Y.fromSpecResidueField (c (closedPoint K))
  have hfac : i ≫ c₀ = c :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y c
  let : IsClosedImmersion c₀ :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_imagePoint c)
  let : IsClosedImmersion (i ≫ c₀) := hfac.symm ▸ inferInstance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i c₀
  let : Surjective i := ⟨fun z => ⟨closedPoint K, Subsingleton.elim _ z⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective i

private theorem closedPoint_ker_eq {Y : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c] :
    c.ker = (Y.fromSpecResidueField (c (closedPoint K))).ker := by
  let : IsIso (Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo c))) :=
    isIso_closedPointResidueFactor c
  exact (congrArg Hom.ker
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y c)).symm.trans
      (Hom.ker_comp_of_isIso _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal fibre of the canonical global point blowup is the local
exceptional projective line, via the actual flat stalk-base-change square. -/
private def canonicalPointFibreIso (Y : Scheme.{u}) (y : Y)
    (hy : IsClosed ({y} : Set Y)) [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hd : ringKrullDim (Y.presheaf.stalk y) = 2) :
    pullback (blowupDatum (Y.fromSpecResidueField y).ker).map
      (Y.fromSpecResidueField y) ≅
        twoChartLine (.of (ResidueField (Y.presheaf.stalk y))) := by
  let R := Y.presheaf.stalk y
  let B := blowupDatum (affineCenter R (maximalIdeal R))
  have h : IsPullback
      (pullback.fst B.map (Spec.map (Y.residue y)) ≫ stalkBlowupComparison Y y hy)
      (pullback.snd B.map (Spec.map (Y.residue y)))
      (blowupDatum (Y.fromSpecResidueField y).ker).map (Y.fromSpecResidueField y) :=
    ((IsPullback.of_hasPullback B.map (Spec.map (Y.residue y))).flip.paste_vert
      (stalkBlowupComparison_isPullback Y y hy).flip).flip
  exact h.isoPullback.symm ≪≫
    (Over.forget _).mapIso (exceptionalOverIsoProjectiveP1 R hd) ≪≫
      (twoChartLineIsoProjectiveP1 (ResidueField R)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The target fibre over the original field point is transported through
its canonical residue factor, retaining the original centre and fibre. -/
private def closedPointFibreIso {Y : Scheme.{u}} {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c]
    [IsRegularLocalRing (Y.presheaf.stalk (c (closedPoint K)))]
    (hd : ringKrullDim (Y.presheaf.stalk (c (closedPoint K))) = 2) :
    pullback (blowupDatum c.ker).map c ≅
      twoChartLine (.of (ResidueField (Y.presheaf.stalk (c (closedPoint K))))) := by
  let i := Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo c))
  let c₀ := Y.fromSpecResidueField (c (closedPoint K))
  let B := blowupDatum c.ker
  let : IsIso i := isIso_closedPointResidueFactor c
  have hfac : c ≫ 𝟙 Y = i ≫ c₀ := by
    simpa only [Category.comp_id] using
      (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y c).symm
  let e : pullback B.map c ≅ pullback B.map c₀ :=
    asIso (pullback.map B.map c B.map c₀ (𝟙 _) i (𝟙 _) (by simp) hfac)
  refine e ≪≫ ?_
  change pullback (blowupDatum c.ker).map c₀ ≅ _
  rw [closedPoint_ker_eq c]
  exact canonicalPointFibreIso Y (c (closedPoint K)) (isClosed_imagePoint c) hd

private theorem imagePoint_ne_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (y : Y) (hd : ringKrullDim (Y.presheaf.stalk y) = 2) : y ≠ genericPoint Y := by
  intro h
  subst y
  change ringKrullDim Y.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

/-- Recognition over an original global closed point only needs regularity
at that point and normality of the actual point blowup. The original full
field, closed-point map and canonical Cartier lift are retained. -/
theorem isIso_lift_of_integral_pointFibre_of_normal
    {Y W : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral W]
    {K : Type u} [Field K] (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c]
    [IsRegularLocalRing (Y.presheaf.stalk (c (closedPoint K)))]
    (hd : ringKrullDim (Y.presheaf.stalk (c (closedPoint K))) = 2)
    (hB : NormalStalks (blowupDatum c.ker).Y)
    (f : W ⟶ Y) [IsProper f] (hf : cartierPullback c.ker f)
    [IsIntegral (pullback f c)]
    (hC : topologicalKrullDim (pullback f c : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement c.ker)] :
    IsIso ((blowupDatum c.ker).lift f hf) := by
  let B := blowupDatum c.ker
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let e := closedPointFibreIso c hd
  let : IsIntegral (pullback B.map c) := IsIntegral.of_isIso e.inv
  have hD : topologicalKrullDim (pullback B.map c : Scheme.{u}) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
      (Scheme.OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim
        (ResidueField (Y.presheaf.stalk (c (closedPoint K)))))
  have hI : genericPoint Y ∉ (c.ker.support : Set Y) := by
    rw [closedPoint_ker_eq c]
    exact genericPoint_not_mem_pointCentre _ (isClosed_imagePoint c)
      (imagePoint_ne_genericPoint _ hd)
  exact B.isIso_lift_of_curve_fibre c f hf hI hB hC.le hD

/-- A proper integral modification of a regular integral locally Noetherian
scheme is its actual closed-point blowup when the point has local dimension
two, the original embedded point ideal pulls back to a Cartier ideal, the
literal point fibre is an integral curve, and the complement map is an
isomorphism. The conclusion is about the original canonical Cartier lift. -/
theorem isIso_lift_of_integral_pointFibre
    {Y W : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral W]
    (hY : RegularStalks Y) {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c]
    (hd : ringKrullDim (Y.presheaf.stalk (c (closedPoint K))) = 2)
    (f : W ⟶ Y) [IsProper f] (hf : cartierPullback c.ker f)
    [IsIntegral (pullback f c)]
    (hC : topologicalKrullDim (pullback f c : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement c.ker)] :
    IsIso ((blowupDatum c.ker).lift f hf) := by
  let : IsRegularLocalRing (Y.presheaf.stalk (c (closedPoint K))) := hY _
  have hregular : RegularStalks (blowupDatum c.ker).Y := by
    rw [closedPoint_ker_eq c]
    exact regularStalks_pointBlowup Y hY _ (isClosed_imagePoint c) hd
  have hnormal : NormalStalks (blowupDatum c.ker).Y := by
    intro z
    let : IsRegularLocalRing ((blowupDatum c.ker).Y.presheaf.stalk z) := hregular z
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  exact isIso_lift_of_integral_pointFibre_of_normal c hd hnormal f hf hC

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open IsLocalRing Scheme.ProjectiveLine.TwoChart

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regularLocalRing_pointBlowup_overPoint
    (Y : Scheme.{u}) (y : Y) (hy : IsClosed ({y} : Set Y))
    [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hd : ringKrullDim (Y.presheaf.stalk y) = 2)
    (z : (blowupDatum (Y.fromSpecResidueField y).ker).Y)
    (hz : (blowupDatum (Y.fromSpecResidueField y).ker).map z = y) :
    IsRegularLocalRing ((blowupDatum (Y.fromSpecResidueField y).ker).Y.presheaf.stalk z) := by
  let B := blowupDatum (Y.fromSpecResidueField y).ker
  have hlocal : RegularStalks (pullback B.map (Y.fromSpecStalk y)) :=
    (regularStalks (Y.presheaf.stalk y) hd).of_isOpenImmersion (stalkBlowupIso Y y hy).inv
  have hlift : z ∈ Set.range (pullback.fst B.map (Y.fromSpecStalk y)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨closedPoint (Y.presheaf.stalk y), Scheme.fromSpecStalk_closedPoint.trans hz.symm⟩
  obtain ⟨w, rfl⟩ := hlift
  let : IsRegularLocalRing ((pullback B.map (Y.fromSpecStalk y)).presheaf.stalk w) := hlocal w
  let : IsIso ((pullback.fst B.map (Y.fromSpecStalk y)).stalkMap w) :=
    stalkBlowupProjection_isIso_stalkMap Y y w
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((pullback.fst B.map (Y.fromSpecStalk y)).stalkMap w)).commRingCatIsoToRingEquiv.symm

/-- Recognition at an original regular closed point is independent of
singularities elsewhere on the target. Only its actual point stalk must be
regular of dimension two; normality is proved on the exceptional fibre. -/
theorem isIso_lift_of_integral_pointFibre_of_regularLocal
    {Y W : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral W]
    {K : Type u} [Field K] (c : Spec (.of K) ⟶ Y) [IsClosedImmersion c]
    [IsRegularLocalRing (Y.presheaf.stalk (c (closedPoint K)))]
    (hd : ringKrullDim (Y.presheaf.stalk (c (closedPoint K))) = 2)
    (f : W ⟶ Y) [IsProper f] (hf : cartierPullback c.ker f)
    [IsIntegral (pullback f c)]
    (hC : topologicalKrullDim (pullback f c : Scheme.{u}) = 1)
    [IsIso (f ∣_ centreComplement c.ker)] :
    IsIso ((blowupDatum c.ker).lift f hf) := by
  let B := blowupDatum c.ker
  let q := B.lift f hf
  let U := B.map ⁻¹ᵁ centreComplement c.ker
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let e := closedPointFibreIso c hd
  let : IsIntegral (pullback B.map c) := IsIntegral.of_isIso e.inv
  have hD : topologicalKrullDim (pullback B.map c : Scheme.{u}) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
      (Scheme.OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim
        (ResidueField (Y.presheaf.stalk (c (closedPoint K)))))
  have hI : genericPoint Y ∉ (c.ker.support : Set Y) := by
    rw [closedPoint_ker_eq c]
    exact genericPoint_not_mem_pointCentre _ (isClosed_imagePoint c)
      (imagePoint_ne_genericPoint _ hd)
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let : IsDominant q := B.lift_isDominant f hf hI
  let : IsIso (q ∣_ U) := B.lift_restrict_isIso f hf
  let : IsFinite q := B.isFinite_lift_of_curve_fibre c f hf hI hC.le hD
  let : Nonempty U := by
    obtain ⟨z, hz⟩ := B.mem_range_of_not_mem_support hI
    exact ⟨⟨z, by change B.map z ∉ (c.ker.support : Set Y); rwa [hz]⟩⟩
  have hnormal : ∀ z : (blowupDatum c.ker).Y,
      (blowupDatum c.ker).map z = c (closedPoint K) →
        IsIntegrallyClosed ((blowupDatum c.ker).Y.presheaf.stalk z) := by
    rw [closedPoint_ker_eq c]
    intro z hz
    let : IsRegularLocalRing
        ((blowupDatum (Y.fromSpecResidueField (c (closedPoint K))).ker).Y.presheaf.stalk z) :=
      regularLocalRing_pointBlowup_overPoint Y _ (isClosed_imagePoint c) hd z hz
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  apply Scheme.isIso_of_isFinite_of_isIso_restrict_of_normal_complement q U
  intro z hz
  apply hnormal z
  have hz' : B.map z ∈ (c.ker.support : Set Y) := by
    change ¬ B.map z ∉ (c.ker.support : Set Y) at hz
    exact not_not.mp hz
  have hs : (c.ker.support : Set Y) = {c (closedPoint K)} := by
    rw [closedPoint_ker_eq c, Hom.support_ker, Scheme.range_fromSpecResidueField,
      (isClosed_imagePoint c).closure_eq]
  exact (congrArg (fun S : Set Y => B.map z ∈ S) hs).mp hz'

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
