/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.TorsionLocus.Kummer

/-! # Finite actual local Kummer charts of the reduced torsion locus

Each chart retains an actual affine chart, an actual open in it, the actual
inverse-image curve family, and an original H1(mu_n) class with the literal
line-bundle Picard image. Compactness of the actual reduced closed parameter
scheme supplies a finite covering family of these charts.

This is finiteness of a geometric covering family, not finiteness of its fibre
classes, Picard torsion, or H1. No proper-base-change conclusion is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge HasExt.standard

universe u v

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (g n : ℕ)

/-- An actual local family chart and one original Kummer preimage on its
literal inverse-image total space. All fields are geometric objects or their
original maps; no fibre finiteness or base-change assertion is included. -/
structure LocalKummerChart where
  /-- The coordinate ring of the actual affine chart. -/
  ring : CommRingCat.{u}
  /-- The original affine open chart in the actual reduced locus. -/
  map : Spec ring ⟶ powerNonvanishingLocus X.hom o ho g n
  /-- The affine chart map is an actual open immersion. -/
  isOpenImmersion_map : IsOpenImmersion map
  /-- The actual open supplied by local power triviality. -/
  openSet : (Spec ring).Opens
  /-- One original class on the literal inverse-image total space. -/
  cohomologyClass : Sheaf.H.{u + 2}
    (mu ((pullback.snd (powerLocusProjection X o ho g n) map) ⁻¹ᵁ openSet).toScheme n) 1
  /-- Its image is the original Picard/frame class of the literal family bundle. -/
  inclusion_cohomologyClass : Sheaf.H.map (inclusion _ n) 1 cohomologyClass =
    EtaleCohomology.Picard.picardCohomologyEquiv _
      (classOf _ (locusChartOpenLineBundle X o ho g n map openSet))

attribute [instance] LocalKummerChart.isOpenImmersion_map

namespace LocalKummerChart

variable {X o ho g n} (C : LocalKummerChart X o ho g n)

/-- The actual base open of this chart. -/
abbrev base : Scheme.{u} := C.openSet.toScheme

/-- Its actual open-immersion map to the reduced parameter locus. -/
def baseMap : C.base ⟶ powerNonvanishingLocus X.hom o ho g n :=
  C.openSet.ι ≫ C.map

instance baseMap_isOpenImmersion : IsOpenImmersion C.baseMap := by
  dsimp only [baseMap]
  infer_instance

/-- The actual inverse-image family over the chosen chart open. -/
abbrev totalSpace : Scheme.{u} :=
  ((pullback.snd (powerLocusProjection X o ho g n) C.map) ⁻¹ᵁ C.openSet).toScheme

/-- The original restricted curve projection. -/
def projection : C.totalSpace ⟶ C.base :=
  (pullback.snd (powerLocusProjection X o ho g n) C.map) ∣_ C.openSet

/-- The original total-space map to the family over the reduced locus. -/
def totalMap : C.totalSpace ⟶ powerLocusCurve X o ho g n :=
  ((pullback.snd (powerLocusProjection X o ho g n) C.map) ⁻¹ᵁ C.openSet).ι ≫
    pullback.fst (powerLocusProjection X o ho g n) C.map

/-- The displayed chart family is an actual Cartesian base change of the
original family over the reduced closed locus. -/
theorem isPullback : IsPullback C.totalMap C.projection
    (powerLocusProjection X o ho g n) C.baseMap :=
  (isPullback_morphismRestrict
    (pullback.snd (powerLocusProjection X o ho g n) C.map) C.openSet).flip.paste_horiz
      (IsPullback.of_hasPullback (powerLocusProjection X o ho g n) C.map)

instance projection_isProper : IsProper C.projection :=
  MorphismProperty.of_isPullback C.isPullback inferInstance

/-- The actual underlying bounded-family bundle on this chart. -/
abbrev lineBundle : LineBundle C.totalSpace :=
  locusChartOpenLineBundle X o ho g n C.map C.openSet

/-- The original inclusion image of the actual chart class. -/
theorem cohomologyClass_image :
    Sheaf.H.map (inclusion C.totalSpace n) 1 C.cohomologyClass =
      EtaleCohomology.Picard.picardCohomologyEquiv C.totalSpace
        (classOf C.totalSpace C.lineBundle) :=
  C.inclusion_cohomologyClass

/-- Actual charts that jointly cover the locus form a native scheme open cover. -/
def openCover {ι : Type v} (C : ι → LocalKummerChart X o ho g n)
    (hC : ∀ z, ∃ i, z ∈ Set.range (C i).baseMap) :
    (powerNonvanishingLocus X.hom o ho g n).OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => (C i).base) (fun i => (C i).baseMap)
    (fun z => by simpa only [Set.mem_range] using hC z)

instance openCover_finite {ι : Type v} [Finite ι]
    (C : ι → LocalKummerChart X o ho g n)
    (hC : ∀ z, ∃ i, z ∈ Set.range (C i).baseMap) :
    Finite (openCover C hC).I₀ := by
  change Finite ι
  infer_instance

end LocalKummerChart

/-- Every actual point of the closed locus lies in an actual local chart
carrying an original Kummer preimage of the literal bounded-family bundle. -/
theorem exists_localKummerChart_mem (hX : Properties X)
    (hn : 0 < n) (hunit : IsUnit (n : k))
    (z : powerNonvanishingLocus X.hom o ho g n) :
    ∃ C : LocalKummerChart X o ho g n, z ∈ Set.range C.baseMap := by
  obtain ⟨R, j, hj, r, hr⟩ := Scheme.exists_Spec_apply_eq z
  let : IsOpenImmersion j := hj
  obtain ⟨U, hrU, ξ, hξ⟩ :=
    exists_locusChartOpen_kummerPreimage X o ho g n j hX hn hunit r
  let C : LocalKummerChart X o ho g n := ⟨R, j, hj, U, ξ, hξ⟩
  refine ⟨C, ⟨⟨r, hrU⟩, ?_⟩⟩
  exact hr

/-- Compactness of the actual reduced closed parameter scheme gives finitely
many actual local families with original Kummer classes covering every point.
Only the number of covering charts is asserted finite. -/
theorem exists_finite_localKummerCharts (hX : Properties X)
    (hn : 0 < n) (hunit : IsUnit (n : k)) :
    ∃ (s : Finset (powerNonvanishingLocus X.hom o ho g n))
      (C : s → LocalKummerChart X o ho g n),
      ∀ z, ∃ i, z ∈ Set.range (C i).baseMap := by
  classical
  choose C hC using exists_localKummerChart_mem X o ho g n hX hn hunit
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover
    (fun z => Set.range (C z).baseMap)
    (fun z => (IsOpenImmersion.isOpen_range (C z).baseMap).mem_nhds (hC z))
  refine ⟨s, fun i => C i.val, ?_⟩
  intro z
  have hz : z ∈ ⋃ x ∈ s, Set.range (C x).baseMap := by rw [hs]; trivial
  simp only [Set.mem_iUnion] at hz
  obtain ⟨x, hx, hzx⟩ := hz
  exact ⟨⟨x, hx⟩, hzx⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
