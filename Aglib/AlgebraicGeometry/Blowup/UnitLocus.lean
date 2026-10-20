/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.CoordinateOverlap

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.UnitLocus`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `630bf7333de91b529ed9c7a840a379cbbd3e040b3fb94c9a1b9c9cdef769c336`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Affine blowup over the complement of its centre

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.Blowup.UnitLocus


/-!
# The actual blowup over basic opens where the centre ideal is the unit ideal

For each a in I, the exact inverse image of D(a) is constructed as Spec A[1/a]
inside the given ordinary blowup, with its structural triangle. All statements
are proved from the same affine atlas; no away-from-centre isomorphism family
is supplied.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.Coordinates
namespace AlgebraicGeometry.Scheme.Blowup.UnitLocus
variable {A : Type u} [CommRing A] (I : Ideal A) (a : I)

/-- Inverting a again in the saturated algebra gives the actual A[1/a]. -/
theorem awayChartIsLocalization : IsLocalization.Away
    (algebraMap A (affineBlowupAlgebra A I a) a) (Localization.Away (a : A)) := by
  apply IsLocalization.Away.mk
  · exact IsLocalization.Away.algebraMap_isUnit (a : A)
  · intro z
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (a : A) z
    exact ⟨n, algebraMap A _ b, hb⟩
  · intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨0, by simp [hxy]⟩

def awayChartEquiv : Localization.Away (algebraMap A (affineBlowupAlgebra A I a) a) ≃ₐ[
    affineBlowupAlgebra A I a] Localization.Away (a : A) := by
  let := awayChartIsLocalization I a
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap A (affineBlowupAlgebra A I a) a)) _ _

/-- The usual relation a*(b/a)=b is an equality in the literal saturated ring. -/
lemma ratio_mul_den (b : I) : ratio A I a b * algebraMap A (affineBlowupAlgebra A I a) a =
    algebraMap A (affineBlowupAlgebra A I a) b := by
  apply Subtype.ext
  simp only [ratio, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (a : A)),
    IsLocalization.Away.mul_invSelf, mul_one]

variable {I a} {B : BlowupDatum (affineCenter A I)} (H : AffineAtlas A I B)

/-- Actual map from Spec A[1/a] onto the blowup over D(a). -/
def unitChartMap (a : I) : Spec (.of (Localization.Away (a : A))) ⟶ B.Y :=
  (Scheme.Spec.mapIso (awayChartEquiv I a).toRingEquiv.toCommRingCatIso.op).hom ≫
    awayMap (algebraMap A (affineBlowupAlgebra A I a) a) ≫ H.chart a

instance unitChartMap_isOpenImmersion (a : I) : IsOpenImmersion (unitChartMap H a) := by
  let := H.openImmersion a
  dsimp only [unitChartMap]
  infer_instance

@[reassoc] lemma unitChartMap_triangle (a : I) :
    unitChartMap H a ≫ B.map = awayMap (a : A) := by
  simp only [unitChartMap, Category.assoc, H.triangle, affineChartMap, awayMap,
    Functor.mapIso_hom, Scheme.Spec, Iso.op_hom, Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (awayChartEquiv I a).commutes (algebraMap A _ z)

lemma unitChartMap_range (a : I) : Set.range (unitChartMap H a) =
    B.map ⁻¹' (PrimeSpectrum.basicOpen (a : A) : Set (PrimeSpectrum A)) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change (unitChartMap H a ≫ B.map) z ∈ PrimeSpectrum.basicOpen (a : A)
    rw [unitChartMap_triangle]
    change PrimeSpectrum.comap (algebraMap A (Localization.Away (a : A))) z ∈ _
    let := z.isPrime
    exact z.asIdeal.notMem_of_isUnit
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : A)) (a : A))
  · intro hy
    obtain ⟨b, x, rfl⟩ := H.covers y
    have hb : algebraMap A (affineBlowupAlgebra A I b) a ∉ x.asIdeal := by
      change (H.chart b ≫ B.map) x ∈ PrimeSpectrum.basicOpen (a : A) at hy
      rw [H.triangle] at hy
      exact hy
    have hr : ratio A I b a ∉ x.asIdeal := by
      intro hr
      apply hb
      rw [← ratio_mul_den I b a]
      exact x.asIdeal.mul_mem_right _ hr
    have hx : x ∈ Set.range (affineOverlapMap A I b a) := by
      change x ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (affineBlowupAlgebra A I b) (Localization.Away (ratio A I b a))))
      rw [PrimeSpectrum.localization_away_comap_range
        (Localization.Away (ratio A I b a)) (ratio A I b a)]
      exact hr
    obtain ⟨z, hz⟩ := hx
    have hyv : H.chart b x ∈ Set.range (affineOverlapMap A I b a ≫ H.chart b) :=
      ⟨z, by change H.chart b (affineOverlapMap A I b a z) = H.chart b x; rw [hz]⟩
    rw [H.overlap] at hyv
    obtain ⟨w, hw⟩ := hyv.2
    have hw' : algebraMap A (affineBlowupAlgebra A I a) a ∉ w.asIdeal := by
      rw [← hw] at hy
      change (H.chart a ≫ B.map) w ∈ PrimeSpectrum.basicOpen (a : A) at hy
      rw [H.triangle] at hy
      exact hy
    have hwloc : w ∈ Set.range (awayMap (algebraMap A (affineBlowupAlgebra A I a) a)) := by
      change w ∈ Set.range (PrimeSpectrum.comap (algebraMap (affineBlowupAlgebra A I a)
        (Localization.Away (algebraMap A (affineBlowupAlgebra A I a) a))))
      rw [PrimeSpectrum.localization_away_comap_range
        (Localization.Away (algebraMap A (affineBlowupAlgebra A I a) a))
          (algebraMap A (affineBlowupAlgebra A I a) a)]
      exact hw'
    obtain ⟨t, ht⟩ := hwloc
    rw [unitChartMap, Scheme.Hom.Range.range_iso_comp]
    exact ⟨t, by change H.chart a (awayMap _ t) = H.chart b x; rw [ht, hw]⟩

/-- The exact inverse-image open, rather than only a set of chart points. -/
def inverseImageBasicOpen (a : I) : B.Y.Opens :=
  B.map ⁻¹ᵁ (PrimeSpectrum.basicOpen (a : A))

/-- The blowup over D(a), a in I, is literally Spec A[1/a]. -/
def unitLocusIso (a : I) : Spec (.of (Localization.Away (a : A))) ≅
    (inverseImageBasicOpen (B := B) a).toScheme :=
  IsOpenImmersion.isoOfRangeEq (unitChartMap H a) (inverseImageBasicOpen (B := B) a).ι
    (by rw [unitChartMap_range, Scheme.Opens.range_ι]; rfl)

@[reassoc] lemma unitLocusIso_hom_triangle (a : I) :
    (unitLocusIso H a).hom ≫ (inverseImageBasicOpen (B := B) a).ι = unitChartMap H a :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc] lemma unitLocusIso_base_triangle (a : I) :
    (unitLocusIso H a).hom ≫ (inverseImageBasicOpen (B := B) a).ι ≫ B.map = awayMap (a : A) := by
  rw [← Category.assoc, unitLocusIso_hom_triangle, unitChartMap_triangle]

/-- These basic opens cover the entire complement of the centre. -/
lemma outside_center_iff (x : PrimeSpectrum A) :
    x ∉ PrimeSpectrum.zeroLocus (I : Set A) ↔ ∃ a : I, x ∈ PrimeSpectrum.basicOpen (a : A) := by
  simp only [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  constructor
  · rintro ⟨a, ha, hx⟩; exact ⟨⟨a, ha⟩, hx⟩
  · rintro ⟨a, ha⟩; exact ⟨a, a.property, ha⟩

end AlgebraicGeometry.Scheme.Blowup.UnitLocus

end
end AlgebraicGeometry.Scheme.Blowup.UnitLocus
