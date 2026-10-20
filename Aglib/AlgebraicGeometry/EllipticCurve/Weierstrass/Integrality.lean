/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.InfinityChart
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Integrality of every Weierstrass cubic over a domain

The affine coordinate ring is the existing native domain. The monic infinity
ring embeds in its actual overlap with that affine ring. The intersecting
two-chart cover proves global integrality, including singular equations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial TensorProduct
universe u v

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R]

lemma affineY_ne_zero [Nontrivial R] (W : WeierstrassCurve R) : affineY W ≠ 0 := by
  change AdjoinRoot.mk W.toAffine.polynomial Polynomial.X ≠ 0
  simpa only [WeierstrassCurve.Affine.CoordinateRing.YClass, map_zero, sub_zero] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := W) (0 : Polynomial R))

/-- The two standard opens intersect over every domain. -/
lemma monicCharts_inter_nonempty [IsDomain R] (W : WeierstrassCurve R) :
    (Set.range (infinityAffineChart W) ∩ Set.range (affineChart W)).Nonempty := by
  let : IsDomain (chartRing W 2) :=
    (affineChartRingEquiv W).symm.toMulEquiv.isDomain _
  let q : PrimeSpectrum (chartRing W 2) := ⟨⊥, inferInstance⟩
  have hy : normalizedCoordinate W 2 1 ≠ 0 := by
    intro h
    have h' := congrArg (fromProjectiveChart W) h
    exact (affineY_ne_zero W) (by simpa using h')
  refine ⟨chart W 2 q, ?_, ?_⟩
  · change chart W 2 q ∈ (infinityAffineChart W).opensRange
    rw [infinityAffineChart_range]
    change coordinate W 1 ∉ (chart W 2 q).asHomogeneousIdeal
    rw [coordinate_mem_chart_iff]
    simpa [q] using hy
  · change chart W 2 q ∈ (affineChart W).opensRange
    rw [affineChart_range, ← chart_range W 2]
    exact ⟨q, rfl⟩

variable [IsDomain R]

/-- The infinity denominator is regular, because this ring is free over `R[v]`. -/
lemma infinityV_mem_nonZeroDivisors (W : WeierstrassCurve R) :
    infinityV W ∈ nonZeroDivisors (infinityRing W) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro a ha
  have hs : (Polynomial.X : Polynomial R) • a = 0 := by
    simpa only [Algebra.smul_def, infinityV, AdjoinRoot.algebraMap_eq] using ha
  exact (smul_eq_zero.mp hs).resolve_left Polynomial.X_ne_zero

/-- The original monic infinity ring embeds in its actual overlap. -/
lemma infinityOverlap_injective (W : WeierstrassCurve R) :
    Function.Injective (algebraMap (infinityRing W) (infinityOverlapRing W)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr (infinityV_mem_nonZeroDivisors W))

/-- Domain of the infinity chart, with no nonsingularity hypothesis. -/
theorem infinityRing_isDomain_of_isDomain (W : WeierstrassCurve R) :
    IsDomain (infinityRing W) := by
  let : IsDomain (affineOverlapRing W) := Localization.Away.isDomain (affineY_ne_zero W)
  let f := (infinityAffineOverlapEquiv W).toRingHom.comp
    (algebraMap (infinityRing W) (infinityOverlapRing W))
  have hf : Function.Injective f :=
    (infinityAffineOverlapEquiv W).injective.comp (infinityOverlap_injective W)
  exact hf.isDomain

/-- The actual `Y` and `Z` scheme charts prove global integrality over every domain. -/
theorem scheme_isIntegral_of_isDomain (W : WeierstrassCurve R) : IsIntegral (scheme W) := by
  let : IsDomain (infinityRing W) := infinityRing_isDomain_of_isDomain W
  let U := monicChartCover W
  have (i : U.I₀) : IsIntegral (U.X i) := by
    cases i <;> change IsIntegral (Spec _) <;> infer_instance
  have : IsReduced (scheme W) := IsReduced.of_openCover _ U
  have hp (i : U.I₀) : PreirreducibleSpace ((U.f i).opensRange) := by
    apply Subtype.preirreducibleSpace
    change IsPreirreducible (Set.range (U.f i))
    simpa only [Set.image_univ] using
      (PreirreducibleSpace.isPreirreducible_univ (X := U.X i)).image
        (U.f i) (U.f i).continuous.continuousOn
  have hpair : Pairwise (fun i j : U.I₀ => ¬ Disjoint (U.f i).opensRange (U.f j).opensRange) := by
    intro i j hij
    obtain ⟨p, hp, hq⟩ := monicCharts_inter_nonempty W
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact fun hd => (show p ∈ (⊥ : (scheme W).Opens) from hd.le_bot ⟨hp, hq⟩)
    · exact fun hd => (show p ∈ (⊥ : (scheme W).Opens) from hd.le_bot ⟨hq, hp⟩)
    · exact False.elim (hij rfl)
  have : PreirreducibleSpace (scheme W) :=
    PreirreducibleSpace.of_isOpenCover hpair U.isOpenCover_opensRange hp
  have : Nonempty (scheme W) := ⟨(monicCharts_inter_nonempty W).choose⟩
  have : IrreducibleSpace (scheme W) := ⟨inferInstance⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end WeierstrassCurve.Projective

/- Migration source: PointedResolution.Weierstrass.Integrality.
Frozen R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 665cf1b80e34b7f832f7c9797c9ca5ae3f1afaf0cfaab3ab014432ba80ffad1f.
Only the unconditional ring/chart proof is selected; no geometry family is supplied. -/
