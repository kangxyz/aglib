/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.Recursion
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.SourceGeometry`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`c72b747d8f34c9fd6db68bac6cf54940fffe3a03574fd40188aaaa75ec4fdb4b`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Structural flatness, reducedness, integrality, chart triangles and surjectivity of the actual
  recursive resolution source.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
universe u

section NodeResolutionBaseGeometry


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Topology
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {n : ℕ}

lemma node_flat (hπ : π ≠ 0) : Module.Flat R (node π n) := by
  let := node_isDomain (π^n) (pow_ne_zero n hπ)
  let : Module.IsTorsionFree R (node π n) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (node_algebraMap_injective (π^n))
  infer_instance

lemma base_flat (hπ : π ≠ 0) : Flat (base (π := π) (n := n)) := by
  rw [base, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (node_flat hπ)

instance base_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (base (π := π) (n := n)) := by
  rw [base, LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap R (node π n)).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

lemma genericOpen_nonempty (hπ : π ≠ 0) : (genericOpen π n : Set (X π n)).Nonempty := by
  let := node_isDomain (π^n) (pow_ne_zero n hπ)
  refine ⟨⟨⊥, inferInstance⟩, ?_⟩
  change algebraMap R (node π n) π ∉ (⊥ : Ideal (node π n))
  simpa only [Ideal.mem_bot, map_zero] using (node_algebraMap_injective (π^n)).ne hπ

lemma genericOpen_dense (hπ : π ≠ 0) : Dense (genericOpen π n : Set (X π n)) := by
  let := node_isDomain (π^n) (pow_ne_zero n hπ)
  exact (genericOpen π n).isOpen.dense (genericOpen_nonempty hπ)

/-- The section U=1, V=pi^n witnesses surjectivity of the literal node over the DVR. -/
def baseSection : Spec (.of R) ⟶ X π n :=
  Spec.map (CommRingCat.ofHom (PlaneNode.lift (π^n) 1 (π^n) (by simp)).toRingHom)

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc] lemma baseSection_triangle :
    baseSection (π := π) (n := n) ≫ base = 𝟙 _ := by
  rw [baseSection, base, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (node π n)) ≫
      CommRingCat.ofHom (PlaneNode.lift (π^n) 1 (π^n) (by simp)).toRingHom = 𝟙 (CommRingCat.of R)
        := by
    apply CommRingCat.hom_ext
    ext r
    exact (PlaneNode.lift (π^n) (1 : R) (π^n) (by simp)).commutes r
  rw [h, Spec.map_id]

instance base_surjective : Surjective (base (π := π) (n := n)) := by
  constructor
  intro p
  have h := baseSection_triangle (π := π) (n := n)
  exact ⟨baseSection p, congr($h p)⟩

variable (D : Data π n)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma genericOpen_subset_range : (genericOpen π n : Set (X π n)) ⊆ Set.range D.map := by
  intro x hx
  obtain ⟨y, hy⟩ := (D.map ∣_ genericOpen π n).surjective ⟨x, hx⟩
  refine ⟨y.val, ?_⟩
  calc
    D.map y.val = (genericOpen π n).ι ((D.map ∣_ genericOpen π n) y) :=
      (congr($(morphismRestrict_ι D.map (genericOpen π n)) y)).symm
    _ = x := congrArg ((genericOpen π n).ι) hy

lemma map_dominant (hπ : π ≠ 0) : IsDominant D.map :=
  ⟨(genericOpen_dense hπ).mono (genericOpen_subset_range D)⟩

/-- Surjectivity follows from the actual proper map and its proved open isomorphism. -/
lemma map_surjective (hπ : π ≠ 0) : Surjective D.map := by
  let := map_dominant D hπ
  infer_instance

lemma source_base_surjective (hπ : π ≠ 0) : Surjective (D.map ≫ base) := by
  let := map_surjective D hπ
  infer_instance

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionBaseGeometry

section NodeResolutionSourceCharts


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OpenPushout.Modification.OfRestriction
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

/-- The actual outer left chart, factored through the unchanged open. -/
def outerLeftChart : Spec (.of (PlaneNode.Ring π)) ⟶ (outerOpen B hπ).toScheme :=
  IsOpenImmersion.lift (outerOpen B hπ).ι (leftChartMap B.atlas hπ) (by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => Or.inl hx)

/-- The right node chart mapped into the union of the two outer chart images. -/
def outerRightChart : Spec (.of (PlaneNode.Ring π)) ⟶ (outerOpen B hπ).toScheme :=
  IsOpenImmersion.lift (outerOpen B hπ).ι (rightChartMap B.atlas hπ) (by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => Or.inr hx)

@[reassoc] lemma outerLeftChart_triangle :
    outerLeftChart B hπ ≫ (outerOpen B hπ).ι = leftChartMap B.atlas hπ :=
  IsOpenImmersion.lift_fac _ _ _
@[reassoc] lemma outerRightChart_triangle :
    outerRightChart B hπ ≫ (outerOpen B hπ).ι = rightChartMap B.atlas hπ :=
  IsOpenImmersion.lift_fac _ _ _

instance outerLeftChart_isOpenImmersion : IsOpenImmersion (outerLeftChart B hπ) := by
  dsimp [outerLeftChart]; infer_instance
instance outerRightChart_isOpenImmersion : IsOpenImmersion (outerRightChart B hπ) := by
  dsimp [outerRightChart]; infer_instance

/-- The left node chart mapped into the glued resolution source through the unchanged outer open. -/
def stepLeftChart : Spec (.of (PlaneNode.Ring π)) ⟶ (step B hπ E).Y :=
  outerLeftChart B hπ ≫ stepUnchangedChart B hπ E
/-- The right node chart mapped into the glued resolution source through the unchanged outer open.
-/
def stepRightChart : Spec (.of (PlaneNode.Ring π)) ⟶ (step B hπ E).Y :=
  outerRightChart B hπ ≫ stepUnchangedChart B hπ E

instance stepLeftChart_isOpenImmersion : IsOpenImmersion (stepLeftChart B hπ E) := by
  dsimp [stepLeftChart]; infer_instance
instance stepRightChart_isOpenImmersion : IsOpenImmersion (stepRightChart B hπ E) := by
  dsimp [stepRightChart]; infer_instance

@[reassoc] lemma stepLeftChart_triangle :
    stepLeftChart B hπ E ≫ (step B hπ E).map =
      Spec.map (CommRingCat.ofHom (leftBase π m).toRingHom) := by
  rw [stepLeftChart, Category.assoc, stepUnchangedChart_triangle,
    outerLeftChart_triangle_assoc, leftChartMap_triangle]

@[reassoc] lemma stepRightChart_triangle :
    stepRightChart B hπ E ≫ (step B hπ E).map =
      Spec.map (CommRingCat.ofHom (rightBase π m).toRingHom) := by
  rw [stepRightChart, Category.assoc, stepUnchangedChart_triangle,
    outerRightChart_triangle_assoc, rightChartMap_triangle]

lemma step_three_charts_cover (z : (step B hπ E).Y) :
    z ∈ Set.range (stepModifiedChart B hπ E) ∨
      z ∈ Set.range (stepLeftChart B hπ E) ∨
      z ∈ Set.range (stepRightChart B hπ E) := by
  rcases charts_cover E.map (middleChartMap B.atlas hπ) (outerOpen B hπ) z with h | h
  · exact Or.inl h
  · obtain ⟨y, rfl⟩ := h
    rcases y.property with ⟨x, hx⟩ | ⟨x, hx⟩
    · right; left; refine ⟨x, ?_⟩
      change stepUnchangedChart B hπ E (outerLeftChart B hπ x) = _
      congr 1
      apply Subtype.ext
      calc
        (outerLeftChart B hπ x).val = leftChartMap B.atlas hπ x :=
          congr($(outerLeftChart_triangle B hπ) x)
        _ = y.val := hx
    · right; right; refine ⟨x, ?_⟩
      change stepUnchangedChart B hπ E (outerRightChart B hπ x) = _
      congr 1
      apply Subtype.ext
      calc
        (outerRightChart B hπ x).val = rightChartMap B.atlas hπ x :=
          congr($(outerRightChart_triangle B hπ) x)
        _ = y.val := hx

/-- The unchanged two affine charts and the actual earlier resolution jointly
cover the new source. No abstract atlas is assumed. -/
def stepCover : (step B hπ E).Y.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 3)
    ![E.Y, Spec (.of (PlaneNode.Ring π)), Spec (.of (PlaneNode.Ring π))]
    (fun | 0 => stepModifiedChart B hπ E
         | 1 => stepLeftChart B hπ E
         | 2 => stepRightChart B hπ E)
    (by
      intro z
      rcases step_three_charts_cover B hπ E z with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩)
    (by intro i; fin_cases i <;> infer_instance)


@[reassoc] lemma stepModifiedChart_base_triangle :
    stepModifiedChart B hπ E ≫ (step B hπ E).map ≫ base = E.map ≫ base := by
  rw [stepModifiedChart_triangle_assoc]
  exact congrArg (E.map ≫ ·) (AlgebraicGeometry.Spec.map_algHom_algebraMap (middleBase π m))

@[reassoc] lemma stepLeftChart_base_triangle :
    stepLeftChart B hπ E ≫ (step B hπ E).map ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  rw [stepLeftChart_triangle_assoc]
  exact AlgebraicGeometry.Spec.map_algHom_algebraMap (leftBase π m)

@[reassoc] lemma stepRightChart_base_triangle :
    stepRightChart B hπ E ≫ (step B hπ E).map ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  rw [stepRightChart_triangle_assoc]
  exact AlgebraicGeometry.Spec.map_algHom_algebraMap (rightBase π m)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionSourceCharts

section NodeResolutionSourceProperties


/-!
# Geometry of the actual recursive source

Flatness and reducedness are proved on the existing recursively constructed
chart cover. The generic-open isomorphism and openness then prove integrality.
The only independent general inputs are still the three ordinary blowup
families. No flatness, integrality, or surjectivity field is supplied to resolve.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Topology
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

lemma uniformizerNode_flat (hπ : Irreducible π) : Module.Flat R (PlaneNode.Ring π) := by
  let := node_isDomain π hπ.ne_zero
  let : Module.IsTorsionFree R (PlaneNode.Ring π) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (node_algebraMap_injective π)
  infer_instance

lemma step_flat [Flat (E.map ≫ base)] : Flat ((step B hπ E).map ≫ base) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (stepCover B hπ E)).mpr
  intro i
  change Fin 3 at i
  fin_cases i
  · change Flat (stepModifiedChart B hπ E ≫ (step B hπ E).map ≫ base)
    rw [stepModifiedChart_base_triangle]
    infer_instance
  · change Flat (stepLeftChart B hπ E ≫ (step B hπ E).map ≫ base)
    rw [stepLeftChart_base_triangle, Flat.SpecMap_iff]
    apply RingHom.flat_algebraMap_iff.mpr
    exact uniformizerNode_flat hπ
  · change Flat (stepRightChart B hπ E ≫ (step B hπ E).map ≫ base)
    rw [stepRightChart_base_triangle, Flat.SpecMap_iff]
    apply RingHom.flat_algebraMap_iff.mpr
    exact uniformizerNode_flat hπ

lemma step_reduced [AlgebraicGeometry.IsReduced E.Y] :
    AlgebraicGeometry.IsReduced (step B hπ E).Y := by
  let := node_isDomain π hπ.ne_zero
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover _ (stepCover B hπ E)).mpr
  intro i
  change Fin 3 at i
  fin_cases i
  · change AlgebraicGeometry.IsReduced E.Y; infer_instance
  · change AlgebraicGeometry.IsReduced (Spec (.of (PlaneNode.Ring π))); infer_instance
  · change AlgebraicGeometry.IsReduced (Spec (.of (PlaneNode.Ring π))); infer_instance

variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})

/-- Flatness of the structure morphism of precisely the recursively glued source. -/
theorem resolve_flat : (n : ℕ) → Flat ((resolve π hπ hex hp ha n).map ≫ base)
  | 0 => by
      change Flat (𝟙 _ ≫ base (π := π) (n := 0))
      rw [Category.id_comp]
      exact base_flat hπ.ne_zero
  | 1 => by
      change Flat (𝟙 _ ≫ base (π := π) (n := 1))
      rw [Category.id_comp]
      exact base_flat hπ.ne_zero
  | m + 2 => by
      let := resolve_flat m
      exact step_flat (OneStepBlowup.ofFamilies π m hex hp ha) hπ _

/-- Reducedness is derived from the actual node charts, with no regular-ring
implies-domain theorem or reduced-source premise. -/
theorem resolve_reduced : (n : ℕ) → AlgebraicGeometry.IsReduced (resolve π hπ hex hp ha n).Y
  | 0 => by
      let := node_isDomain (π^0) (pow_ne_zero 0 hπ.ne_zero)
      change AlgebraicGeometry.IsReduced (X π 0)
      infer_instance
  | 1 => by
      let := node_isDomain (π^1) (pow_ne_zero 1 hπ.ne_zero)
      change AlgebraicGeometry.IsReduced (X π 1)
      infer_instance
  | m + 2 => by
      let := resolve_reduced m
      exact step_reduced (OneStepBlowup.ofFamilies π m hex hp ha) hπ _

variable {π} {n : ℕ} (D : Data π n)

instance source_base_locallyOfFinitePresentation : LocallyOfFinitePresentation (D.map ≫ base) := by
  infer_instance

lemma source_genericOpen_dense (hπ : π ≠ 0) [Flat (D.map ≫ base)] :
    Dense ((D.map ⁻¹ᵁ genericOpen π n : D.Y.Opens) : Set D.Y) := by
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen π
  have h : Dense (U : Set (Spec (.of R))) :=
    U.isOpen.dense ⟨⟨⊥, inferInstance⟩, by
      change π ∉ (⊥ : Ideal R)
      simpa only [Ideal.mem_bot] using hπ⟩
  exact h.preimage (D.map ≫ base).isOpenMap

lemma source_genericOpen_integral (hπ : π ≠ 0) :
    IsIntegral (D.map ⁻¹ᵁ genericOpen π n).toScheme := by
  let := node_isDomain (π^n) (pow_ne_zero n hπ)
  let : Nonempty (genericOpen π n).toScheme := (genericOpen_nonempty hπ).to_subtype
  let : IsIntegral (genericOpen π n).toScheme :=
    isIntegral_of_isOpenImmersion (genericOpen π n).ι
  exact IsIntegral.of_isIso (genericIso D).inv

lemma source_integral_of_flat_reduced (hπ : π ≠ 0) [Flat (D.map ≫ base)]
    [AlgebraicGeometry.IsReduced D.Y] : IsIntegral D.Y := by
  let := source_genericOpen_integral D hπ
  have hi : IsIrreducible ((D.map ⁻¹ᵁ genericOpen π n : D.Y.Opens) : Set D.Y) := by
    have h := (IrreducibleSpace.isIrreducible_univ
      (D.map ⁻¹ᵁ genericOpen π n).toScheme).image (D.map ⁻¹ᵁ genericOpen π n).ι
        (D.map ⁻¹ᵁ genericOpen π n).ι.continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using h
  let : IrreducibleSpace D.Y := (irreducibleSpace_def D.Y).mpr (by
    change IsIrreducible (Set.univ : Set D.Y)
    rw [← (source_genericOpen_dense D hπ).closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced D.Y

/-- Integrality of the same actual source, proved after flatness and reducedness. -/
theorem resolve_integral (n : ℕ) : IsIntegral (resolve π hπ hex hp ha n).Y := by
  let := resolve_flat π hπ hex hp ha n
  let := resolve_reduced π hπ hex hp ha n
  exact source_integral_of_flat_reduced _ hπ.ne_zero

/-- The actual proper resolution map is surjective, with no surjectivity premise. -/
theorem resolve_surjective (n : ℕ) : Surjective (resolve π hπ hex hp ha n).map :=
  map_surjective _ hπ.ne_zero

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionSourceProperties
