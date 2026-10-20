/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Affine
public import Aglib.AlgebraicGeometry.AffineScheme.StructureMap
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometry of the pinched projective line

The literal affine normalization glues to a finite surjective map. The actual
spectrum fibre consists of the two displayed branches. Separatedness follows
from the surjective overlap tensor map; normality and integrality use the same charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.PinchedLine

open Polynomial.PinchedPair

variable (k : Type u) [Field k]

namespace GluingNormality

private theorem affine_normalStalk (B : Type u) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (x : Spec (.of B)) :
    IsDomain ((Spec (.of B)).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) :=
  (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec B x).symm

private theorem open_normalStalk {U X : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (x : U)
    (h : IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x)) :
    IsDomain (X.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (X.presheaf.stalk (f x)) := by
  let := h.1
  let := h.2
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
end GluingNormality

section ConcreteGluing

/-- The conductor open has exactly its expected inverse image under the actual
finite affine normalization. -/
theorem conductor_preimage :
    normalizationMap k ⁻¹ᵁ (gluingToNode k).opensRange =
      (normalizationOverlapInclusion k).opensRange := by
  change normalizationMap k ⁻¹ᵁ
    ((conductorOpenIso k).hom ≫ nodeOverlapInclusion k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  have hn : (nodeOverlapInclusion k).opensRange = PrimeSpectrum.basicOpen (conductor k) :=
    Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k)) (conductor k)
  have ha : (normalizationOverlapInclusion k).opensRange =
      PrimeSpectrum.basicOpen (conductor k : Polynomial k) :=
    Scheme.Hom.opensRange_localizationAway (R := .of (Polynomial k)) (conductor k : Polynomial k)
  rw [hn, ha]
  ext p
  rfl

/-- Global finiteness is derived from the two genuine chart pullback squares. -/
instance gluedNormalizationMap_finite : IsFinite (gluedNormalizationMap k) := by
  let := normalizationMap_finite k
  exact OpenNormalizationGluing.normalizationMap_finite (gluingToNode k) (gluingToInfinity k)
    (normalizationOverlapInclusion k) (normalizationMap k)
    (conductorOpenIso_over k).symm (conductor_preimage k)

/-- The affine normalization chart is literally the pullback of the affine
chart of the glued scheme. -/
theorem gluedNormalizationMap_affine_isPullback :
    IsPullback (normalizationMap k)
      (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k))
      (pushout.inl (gluingToNode k) (gluingToInfinity k)) (gluedNormalizationMap k) :=
  OpenNormalizationGluing.affine_isPullback (gluingToNode k) (gluingToInfinity k)
    (normalizationOverlapInclusion k) (normalizationMap k) (conductorOpenIso_over k).symm

/-- The infinity pullback is the identity chart, proved using the conductor
inverse-image equality rather than assumed as gluing data. -/
theorem gluedNormalizationMap_infinity_isPullback :
    IsPullback (𝟙 (Spec (.of (infinityChartRing k))))
      (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k))
      (pushout.inr (gluingToNode k) (gluingToInfinity k)) (gluedNormalizationMap k) :=
  OpenNormalizationGluing.infinity_isPullback (gluingToNode k) (gluingToInfinity k)
    (normalizationOverlapInclusion k) (normalizationMap k)
    (conductorOpenIso_over k).symm (conductor_preimage k)


theorem normalizationMap_over : normalizationMap k ≫ Spec.algebraMap k (nodeRing k) =
    Spec.algebraMap k k[X] := Spec.map_algHom_algebraMap (nodeRing k).val

theorem normalizationOverlapInclusion_over : normalizationOverlapInclusion k ≫ Spec.algebraMap k
  k[X] =
    Spec.algebraMap k (normalizationOverlapRing k) :=
  Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom k k[X] (normalizationOverlapRing k))

theorem gluingToNode_over : gluingToNode k ≫ Spec.algebraMap k (nodeRing k) =
    Spec.algebraMap k (normalizationOverlapRing k) := by
  rw [gluingToNode, conductorOpenIso_over, Category.assoc, normalizationMap_over,
    normalizationOverlapInclusion_over]

theorem infinityOverlapInclusion_over : infinityOverlapInclusion k ≫ Spec.algebraMap k
  (infinityChartRing k) =
    Spec.algebraMap k (infinityOverlapRing k) :=
  Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom k (infinityChartRing k) (infinityOverlapRing
    k))

theorem standardOverlapSpecIso_over : (standardOverlapSpecIso k).hom ≫ Spec.algebraMap k
  (infinityOverlapRing k) =
    Spec.algebraMap k (normalizationOverlapRing k) := by
  exact Spec.map_algHom_algebraMap ((standardOverlapEquiv k).symm.restrictScalars k).toAlgHom

theorem reciprocalSchemeIso_over : (reciprocalSchemeIso k).hom ≫
    Spec.algebraMap k (normalizationOverlapRing k) = Spec.algebraMap k (normalizationOverlapRing
      k) :=
  Spec.map_algHom_algebraMap (ConductorReciprocal.reciprocalEquiv k).toAlgHom

theorem gluingToInfinity_over : gluingToInfinity k ≫ Spec.algebraMap k (infinityChartRing k) =
    Spec.algebraMap k (normalizationOverlapRing k) := by
  simp only [gluingToInfinity, canonicalInfinityOpen, Category.assoc,
    infinityOverlapInclusion_over, standardOverlapSpecIso_over, reciprocalSchemeIso_over]

/-- The field structure map obtained by gluing the pinched affine and infinity chart maps. -/
def pinchedStructure : pinchedGluing k ⟶ Spec (.of k) :=
  pushout.desc (Spec.algebraMap k (nodeRing k)) (Spec.algebraMap k (infinityChartRing k))
    (by rw [gluingToNode_over, gluingToInfinity_over])

/-- The field structure map obtained by gluing the affine-line and infinity chart maps. -/
def lineStructure : lineGluing k ⟶ Spec (.of k) :=
  pushout.desc (Spec.algebraMap k k[X]) (Spec.algebraMap k (infinityChartRing k))
    (by rw [normalizationOverlapInclusion_over, gluingToInfinity_over])

theorem gluedNormalizationMap_over : gluedNormalizationMap k ≫ pinchedStructure k = lineStructure
  k := by
  apply pushout.hom_ext
  · rw [← Category.assoc, gluedNormalizationMap_affine, Category.assoc]
    simp only [pinchedStructure, lineStructure, pushout.inl_desc, normalizationMap_over]
  · rw [← Category.assoc, gluedNormalizationMap_infinity, pinchedStructure, lineStructure,
      pushout.inr_desc, pushout.inr_desc]
/-- The actual prime ideal of evaluation at a on the affine line. -/
def branchPoint (a : k) : normalizationScheme k :=
  ⟨RingHom.ker (evalRingHom a), (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
    (fun x => ⟨C x, by simp⟩)).isPrime⟩

theorem branchPoint_eq_of_mem (p : normalizationScheme k) (a : k)
    (h : X - C a ∈ p.asIdeal) : p = branchPoint k a := by
  apply PrimeSpectrum.ext
  symm
  apply (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
    (fun x => ⟨C x, by simp⟩)).eq_of_le p.isPrime.ne_top
  rw [ker_evalRingHom]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)

theorem branchPoint_conductor (p : normalizationScheme k)
    (hq : (conductor k : k[X]) ∈ p.asIdeal) :
    p = branchPoint k 0 ∨ p = branchPoint k 1 := by
  obtain h | h := p.isPrime.mem_or_mem hq
  · left
    exact branchPoint_eq_of_mem k p 0 (by simpa using h)
  · right
    exact branchPoint_eq_of_mem k p 1 (by simpa using h)

theorem branchPoint_distinct : branchPoint k 0 ≠ branchPoint k 1 := by
  intro h
  have hmem : (X : k[X]) ∈ (branchPoint k 0).asIdeal := by simp [branchPoint]
  rw [h] at hmem
  simp [branchPoint] at hmem

theorem branchPoint_same_image :
    normalizationMap k (branchPoint k 0) = normalizationMap k (branchPoint k 1) := by
  apply PrimeSpectrum.ext
  ext a
  change eval 0 (a : k[X]) = 0 ↔ eval 1 (a : k[X]) = 0
  rw [(mem_nodeRing k a).mp a.property]

/-- Exhaustion of the entire spectrum fibre by the two explicit prime ideals. -/
theorem affine_normalization_fibre (p : normalizationScheme k) :
    normalizationMap k p = normalizationMap k (branchPoint k 0) ↔
      p = branchPoint k 0 ∨ p = branchPoint k 1 := by
  constructor
  · intro h
    apply branchPoint_conductor k p
    have hq : conductor k ∈ (normalizationMap k (branchPoint k 0)).asIdeal := by
      change eval 0 (X * (X - 1) : k[X]) = 0
      simp
    rw [← h] at hq
    exact hq
  · rintro (rfl | rfl)
    · rfl
    · exact (branchPoint_same_image k).symm

/-- The affine normalization point with coordinate `a`, viewed in the glued projective line. -/
def gluedBranchPoint (a : k) : lineGluing k :=
  pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) (branchPoint k a)

/-- The pinched node, viewed in the affine chart of the glued curve. -/
def gluedNodePoint : pinchedGluing k :=
  pushout.inl (gluingToNode k) (gluingToInfinity k)
    (normalizationMap k (branchPoint k 0))

theorem nodePoint_not_on_overlap (w : Spec (.of (normalizationOverlapRing k))) :
    gluingToNode k w ≠ normalizationMap k (branchPoint k 0) := by
  intro h
  have hw : normalizationMap k (branchPoint k 0) ∈ (gluingToNode k).opensRange := ⟨w, h⟩
  have hn : (gluingToNode k).opensRange = PrimeSpectrum.basicOpen (conductor k) := by
    change ((conductorOpenIso k).hom ≫ nodeOverlapInclusion k).opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k)) (conductor k)
  rw [hn] at hw
  apply hw
  change eval 0 (X * (X - 1) : k[X]) = 0
  simp

theorem gluedBranchPoint_distinct : gluedBranchPoint k 0 ≠ gluedBranchPoint k 1 := by
  intro h
  apply branchPoint_distinct k
  exact (pushout.inl (normalizationOverlapInclusion k)
    (gluingToInfinity k)).isOpenEmbedding.injective h

/-- Every point of the global fibre is one of the two explicit affine branches;
no additional point comes from the infinity chart. -/
theorem glued_normalization_fibre (z : lineGluing k) :
    gluedNormalizationMap k z = gluedNodePoint k ↔
      z = gluedBranchPoint k 0 ∨ z = gluedBranchPoint k 1 := by
  have hh := OpenNormalizationGluing.normalization_fibre
    (gluingToNode k) (gluingToInfinity k) (normalizationOverlapInclusion k)
    (normalizationMap k) (conductorOpenIso_over k).symm
    (normalizationMap k (branchPoint k 0)) (nodePoint_not_on_overlap k) z
  change gluedNormalizationMap k z = gluedNodePoint k ↔
      ∃ x, normalizationMap k x = normalizationMap k (branchPoint k 0) ∧
        pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k) x = z at hh
  rw [hh]
  simp only [affine_normalization_fibre]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rcases hx with rfl | rfl
    · exact Or.inl hxz.symm
    · exact Or.inr hxz.symm
  · rintro (rfl | rfl)
    · exact ⟨branchPoint k 0, Or.inl rfl, rfl⟩
    · exact ⟨branchPoint k 1, Or.inr rfl, rfl⟩

/-- Cardinality of the actual scheme-map fibre, derived from the two distinct
prime ideals and the chart pullback equations. -/
theorem glued_normalization_fibre_card :
    Nat.card {z : lineGluing k // gluedNormalizationMap k z = gluedNodePoint k} = 2 := by
  change ({z : lineGluing k | gluedNormalizationMap k z = gluedNodePoint k} : Set _).ncard = 2
  have he : {z : lineGluing k | gluedNormalizationMap k z = gluedNodePoint k} =
      {gluedBranchPoint k 0, gluedBranchPoint k 1} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      glued_normalization_fibre]
  rw [he, Set.ncard_pair (gluedBranchPoint_distinct k)]

/-- Finite generation of the actual pinched coordinate algebra follows from
Artin–Tate, not from a supplied presentation certificate. -/
instance nodeRing_finiteType : Algebra.FiniteType k (nodeRing k) :=
  ⟨fg_of_fg_of_fg k (nodeRing k) k[X]
    Algebra.FiniteType.out Module.Finite.fg_top Subtype.val_injective⟩


/-- The pinched curve is locally of finite type over `k`. -/
instance pinchedStructure_finiteType : LocallyOfFiniteType (pinchedStructure k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (OpenNormalizationGluing.twoChartCover (gluingToNode k) (gluingToInfinity k))
  intro b
  cases b
  · change LocallyOfFiniteType (pushout.inl (gluingToNode k) (gluingToInfinity k) ≫
    pinchedStructure k)
    simp only [pinchedStructure, pushout.inl_desc]
    infer_instance
  · change LocallyOfFiniteType (pushout.inr (gluingToNode k) (gluingToInfinity k) ≫
    pinchedStructure k)
    simp only [pinchedStructure, pushout.inr_desc]
    infer_instance

/-- The normalization gluing is locally of finite type over `k`. -/
instance lineStructure_finiteType : LocallyOfFiniteType (lineStructure k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (OpenNormalizationGluing.twoChartCover (normalizationOverlapInclusion k) (gluingToInfinity k))
  intro b
  cases b
  · change LocallyOfFiniteType (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k)
    ≫ lineStructure k)
    simp only [lineStructure, pushout.inl_desc]
    infer_instance
  · change LocallyOfFiniteType (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)
    ≫ lineStructure k)
    simp only [lineStructure, pushout.inr_desc]
    infer_instance


theorem normalizationMap_surjective : Function.Surjective (normalizationMap k) := by
  exact RingHom.IsIntegral.comap_surjective
    ((algebraMap_isIntegral_iff).mpr (inferInstance : Algebra.IsIntegral (nodeRing k) (Polynomial
      k)))
    Subtype.val_injective

theorem gluedNormalizationMap_surjective : Function.Surjective (gluedNormalizationMap k) :=
  OpenNormalizationGluing.normalizationMap_surjective (gluingToNode k) (gluingToInfinity k)
    (normalizationOverlapInclusion k) (normalizationMap k) (conductorOpenIso_over k).symm
    (normalizationMap_surjective k)

/-- The normalization map of the glued pinched curve is surjective. -/
instance gluedNormalizationMap_surjective_instance : Surjective (gluedNormalizationMap k) :=
  ⟨gluedNormalizationMap_surjective k⟩



namespace GluingNormality


variable (k : Type u) [Field k]

theorem infinityChart_normalStalk (x : Spec (.of (infinityChartRing k))) :
    IsDomain ((Spec (.of (infinityChartRing k))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec (.of (infinityChartRing k))).presheaf.stalk x) := by
  have h : (X - 1 : k[X]) ≠ 0 := by simpa only [C_1] using X_sub_C_ne_zero (1 : k)
  let : IsDomain (infinityChartRing k) := IsLocalization.Away.isDomain (infinityChartRing k) h
  let : IsIntegrallyClosed (infinityChartRing k) :=
    isIntegrallyClosed_of_isLocalization (infinityChartRing k) (Submonoid.powers (X - 1 : k[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors h)
  exact affine_normalStalk (infinityChartRing k) x

theorem lineGluing_normalStalks (x : lineGluing k) :
    IsDomain ((lineGluing k).presheaf.stalk x) ∧
      IsIntegrallyClosed ((lineGluing k).presheaf.stalk x) := by
  rcases lineGluing_covered k x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact open_normalStalk
      (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k)) y
      (affine_normalStalk k[X] y)
  · exact open_normalStalk
      (pushout.inr (normalizationOverlapInclusion k) (gluingToInfinity k)) y
      (infinityChart_normalStalk k y)

end GluingNormality

/-- Actual normality of every stalk of the glued source. -/
theorem lineGluing_normal : NormalStalks (lineGluing k) := GluingNormality.lineGluing_normalStalks k
section ConcreteSeparation
open ConductorReciprocal
open scoped TensorProduct

theorem gluingToNode_spec : gluingToNode k =
    Spec.map (CommRingCat.ofHom (affineOverlapRingMap k).toRingHom) := by
  rw [gluingToNode, conductorOpenIso_over]
  unfold normalizationOverlapInclusion normalizationMap affineOverlapRingMap
  rw [← Spec.map_comp]
  rfl

theorem gluingToInfinity_spec : gluingToInfinity k =
    Spec.map (CommRingCat.ofHom (infinityOverlapRingMap k).toRingHom) := by
  change (Spec.map _) ≫ ((Spec.map _) ≫ Spec.map _) = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The common overlap mapped into the product over `k` of the two pinched-curve charts. -/
def overlapToProduct : Spec (.of (normalizationOverlapRing k)) ⟶
    pullback (Spec.algebraMap k (nodeRing k)) (Spec.algebraMap k (infinityChartRing k)) :=
  pullback.lift (gluingToNode k) (gluingToInfinity k)
    ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)

theorem overlapToProduct_eq : overlapToProduct k =
    Spec.map (CommRingCat.ofHom (R := nodeRing k ⊗[k] infinityChartRing k)
      (S := W k) (overlapTensorMap k).toRingHom) ≫
      (pullbackSpecIso k (nodeRing k) (infinityChartRing k)).inv := by
  apply pullback.hom_ext
  · erw [overlapToProduct, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      gluingToNode_spec, ← Spec.map_comp]
    congr 1
    ext x
    simp [overlapTensorMap]
  · erw [overlapToProduct, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      gluingToInfinity_spec, ← Spec.map_comp]
    congr 1
    ext x
    simp [overlapTensorMap]

theorem overlapTensorMap_closedImmersion :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (R := nodeRing k ⊗[k] infinityChartRing k)
      (S := W k) (overlapTensorMap k).toRingHom)) := by
  apply IsClosedImmersion.spec_of_surjective
  exact overlapTensorMap_surjective k

/-- The common overlap is a closed subscheme of the product of the two charts over `k`. -/
instance overlapToProduct_closedImmersion : IsClosedImmersion (overlapToProduct k) := by
  rw [overlapToProduct_eq]
  let := overlapTensorMap_closedImmersion k
  exact IsClosedImmersion.comp _ _

/-- The actual gluing is separated: the tensor overlap map is surjective,
so the overlap embeds closedly in the product of the two affine charts. -/
instance pinchedStructure_separated : IsSeparated (pinchedStructure k) := by
  have : IsSeparated (Spec.algebraMap k (nodeRing k)) := by
    unfold Spec.algebraMap
    infer_instance
  have : IsSeparated (Spec.algebraMap k (infinityChartRing k)) := by
    unfold Spec.algebraMap
    infer_instance
  have : IsClosedImmersion (pullback.lift (gluingToNode k) (gluingToInfinity k)
      ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)) :=
    overlapToProduct_closedImmersion k
  exact SeparatedGluing.separated_desc (gluingToNode k) (gluingToInfinity k)
    (Spec.algebraMap k (nodeRing k)) (Spec.algebraMap k (infinityChartRing k))
    ((gluingToNode_over k).trans (gluingToInfinity_over k).symm)

end ConcreteSeparation

/-- Two compact affine charts make these actual glued schemes quasi-compact. -/
instance pinchedGluing_compactSpace : CompactSpace (pinchedGluing k) :=
  openPushout_compactSpace (gluingToNode k) (gluingToInfinity k)

/-- The underlying space of the normalization gluing is compact. -/
instance lineGluing_compactSpace : CompactSpace (lineGluing k) :=
  openPushout_compactSpace (normalizationOverlapInclusion k) (gluingToInfinity k)

/-- The structure map of the pinched curve is quasi-compact. -/
instance pinchedStructure_quasiCompact : QuasiCompact (pinchedStructure k) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- The structure map of the normalization gluing is quasi-compact. -/
instance lineStructure_quasiCompact : QuasiCompact (lineStructure k) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

/-- The pinched curve is locally Noetherian. -/
instance pinchedGluing_locallyNoetherian : IsLocallyNoetherian (pinchedGluing k) :=
  LocallyOfFiniteType.isLocallyNoetherian (pinchedStructure k)

/-- The normalization gluing is locally Noetherian. -/
instance lineGluing_locallyNoetherian : IsLocallyNoetherian (lineGluing k) :=
  LocallyOfFiniteType.isLocallyNoetherian (lineStructure k)

private theorem openPushout_inl_denseRange {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] [Nonempty W] [IrreducibleSpace V] :
    DenseRange (pushout.inl f g) := by
  have hg : DenseRange g := g.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace g
  intro z
  rcases openPushout_covered f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨x, rfl⟩
  · refine hg.induction_on (p := fun v => pushout.inr f g v ∈ closure (Set.range (pushout.inl f g)))
      y (isClosed_closure.preimage (pushout.inr f g).continuous) ?_
    intro w
    rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply]
    exact subset_closure ⟨f w, rfl⟩

private theorem openPushout_irreducibleSpace {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] [Nonempty W]
    [IrreducibleSpace U] [IrreducibleSpace V] :
    IrreducibleSpace (pushout f g : Scheme.{u}) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (pushout f g : Scheme.{u}))
  have hi : IsIrreducible (Set.range (pushout.inl f g)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ U).image _ (pushout.inl f g).continuous.continuousOn
  simpa only [(openPushout_inl_denseRange f g).closure_range] using hi.closure

/-- The conductor localization of the polynomial normalization ring is a domain. -/
instance normalizationOverlapRing_domain : IsDomain (normalizationOverlapRing k) :=
  IsLocalization.Away.isDomain (normalizationOverlapRing k) (conductor_ne_zero k)

/-- The infinity chart ring is a domain. -/
instance infinityChartRing_domain : IsDomain (infinityChartRing k) :=
  IsLocalization.Away.isDomain (infinityChartRing k)
    (by simpa only [C_1] using X_sub_C_ne_zero (1 : k))

/-- The underlying space of the normalization gluing is irreducible. -/
instance lineGluing_irreducibleSpace : IrreducibleSpace (lineGluing k) :=
  openPushout_irreducibleSpace (normalizationOverlapInclusion k) (gluingToInfinity k)

/-- The underlying space of the pinched curve is irreducible. -/
instance pinchedGluing_irreducibleSpace : IrreducibleSpace (pinchedGluing k) :=
  openPushout_irreducibleSpace (gluingToNode k) (gluingToInfinity k)

/-- The normalization gluing is an integral scheme. -/
instance lineGluing_integral : IsIntegral (lineGluing k) := by
  let := (lineGluing_normal k).isReduced
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The pinched curve is an integral scheme. -/
instance pinchedGluing_integral : IsIntegral (pinchedGluing k) := by
  let C := OpenNormalizationGluing.twoChartCover (gluingToNode k) (gluingToInfinity k)
  let (i : C.I₀) : IsReduced (C.X i) := by cases i <;> dsimp [C,
    OpenNormalizationGluing.twoChartCover] <;> infer_instance
  let := IsReduced.of_openCover (pinchedGluing k) C
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Separatedness of the source also follows from the finite map and the
proved separatedness of its target structure. -/
instance lineStructure_separated : IsSeparated (lineStructure k) := by
  rw [← gluedNormalizationMap_over]
  infer_instance

/-- There is exactly one actual irreducible component, derived from the
explicit open gluing. This is not a supplied vertex certificate. -/
theorem pinchedGluing_components_card :
    Nat.card (irreducibleComponents (pinchedGluing k)) = 1 := by
  simp [irreducibleComponents_eq_singleton]
end ConcreteGluing

end AlgebraicGeometry.Scheme.PinchedLine

/- Migration source: R5Lab/AlgebraicGeometry/Curves/Nodal/Gluing.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 8cec975155b7d08159638151bf8e81508669bb2038fc2162a8774fb6c65b1276.
Affine normal-stalk data reuses the native theorem; local transports retain
the proofs from R5Lab/Aglib/AlgebraicGeometry/Stalk/NormalAffine.lean. -/
