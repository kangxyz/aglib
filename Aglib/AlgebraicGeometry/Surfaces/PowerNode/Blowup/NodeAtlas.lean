/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Blowup.CoordinateOverlap
public import Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas
public import Aglib.RingTheory.Blowup.PowerNode.Overlaps

/-!
Native extraction from the R5 local-model source
`PointedResolution.Blowup.NodeAtlas`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`a786f98bfeb62e901d66f2dba512492aef1c02bb1815591452aee9179d96913c`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# The actual three-chart node blowup atlas, exact principal-open scheme overlaps, finite coverage
  and conditional one-step proper blowup.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.Hom.Range Localization.Away
universe u

section AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas


/-!
# The three actual charts of one literal node blowup

This file consumes the frozen saturated algebra equivalences and the precise
ordinary `AffineAtlas` object. The three-chart covering is derived, not assumed.
All maps target the same actual `BlowupDatum.Y` and preserve its blowdown.
No existence, properness, regularity, or resolution theorem is asserted here.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Blowup _root_.PowerNode.Rees
open PlaneNode
namespace AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
variable {R : Type u} [CommRing R]

/-- The three literal generators, in the order u, pi, v. -/
def generator (π : R) (m : ℕ) : Fin 3 → centerIdeal π (m + 2) :=
  ![⟨PlaneNode.U (π^(m + 2)), Ideal.subset_span (by simp)⟩,
    ⟨algebraMap R _ π, Ideal.subset_span (by simp)⟩,
    ⟨PlaneNode.V (π^(m + 2)), Ideal.subset_span (by simp)⟩]

lemma generator_span (π : R) (m : ℕ) :
    Ideal.span (Set.range fun i => (generator π m i : node π (m + 2))) =
      centerIdeal π (m + 2) := by
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [generator]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩

variable [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π) (m : ℕ)

/-- Identify the node with parameter `π` with the left affine chart of the exponent-`m + 2` blowup.
-/
def leftIso : Spec (.of (PlaneNode.Ring π)) ≅
    Spec (.of (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2))
      (generator π m 0))) :=
  Scheme.Spec.mapIso (dvrLeftReesEquiv π hπ m).symm.toRingEquiv.toCommRingCatIso.op

/-- Identify the exponent-`m` node with the middle affine chart of the exponent-`m + 2` blowup. -/
def middleIso : Spec (.of (node π m)) ≅
    Spec (.of (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2))
      (generator π m 1))) :=
  Scheme.Spec.mapIso (dvrMiddleReesEquiv π hπ m).symm.toRingEquiv.toCommRingCatIso.op

/-- Identify the node with parameter `π` with the right affine chart of the exponent-`m + 2` blowup.
-/
def rightIso : Spec (.of (PlaneNode.Ring π)) ≅
    Spec (.of (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2))
      (generator π m 2))) :=
  Scheme.Spec.mapIso (dvrRightReesEquiv π hπ m).symm.toRingEquiv.toCommRingCatIso.op

variable {π hπ m}
variable {B : BlowupDatum (affineCenter (node π (m + 2)) (centerIdeal π (m + 2)))}
variable (H : AffineAtlas (node π (m + 2)) (centerIdeal π (m + 2)) B)

/-- The actual open u-chart into the given blowup. -/
def leftChartMap (hπ : Irreducible π) : Spec (.of (PlaneNode.Ring π)) ⟶ B.Y :=
  (leftIso π hπ m).hom ≫ H.chart (generator π m 0)
/-- The actual open pi-chart into the same given blowup. -/
def middleChartMap (hπ : Irreducible π) : Spec (.of (node π m)) ⟶ B.Y :=
  (middleIso π hπ m).hom ≫ H.chart (generator π m 1)
/-- The actual open v-chart into the same given blowup. -/
def rightChartMap (hπ : Irreducible π) : Spec (.of (PlaneNode.Ring π)) ⟶ B.Y :=
  (rightIso π hπ m).hom ≫ H.chart (generator π m 2)

instance leftChartMap_isOpenImmersion (hπ : Irreducible π) :
    IsOpenImmersion (leftChartMap H hπ) := by
  let := H.openImmersion (generator π m 0)
  dsimp [leftChartMap]; infer_instance
instance middleChartMap_isOpenImmersion (hπ : Irreducible π) :
    IsOpenImmersion (middleChartMap H hπ) := by
  let := H.openImmersion (generator π m 1)
  dsimp [middleChartMap]; infer_instance
instance rightChartMap_isOpenImmersion (hπ : Irreducible π) :
    IsOpenImmersion (rightChartMap H hπ) := by
  let := H.openImmersion (generator π m 2)
  dsimp [rightChartMap]; infer_instance

@[reassoc] lemma leftChartMap_triangle (hπ : Irreducible π) :
    leftChartMap H hπ ≫ B.map = Spec.map (CommRingCat.ofHom (leftBase π m).toRingHom) := by
  rw [leftChartMap, Category.assoc, H.triangle]
  change Spec.map (CommRingCat.ofHom (dvrLeftReesEquiv π hπ m).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (node π (m + 2))
      (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 0)))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (AlgEquiv.symm_apply_eq (dvrLeftReesEquiv π hπ m)).mpr
    (dvrLeftReesEquiv_base π hπ m z).symm

@[reassoc] lemma middleChartMap_triangle (hπ : Irreducible π) :
    middleChartMap H hπ ≫ B.map = Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) := by
  rw [middleChartMap, Category.assoc, H.triangle]
  change Spec.map (CommRingCat.ofHom (dvrMiddleReesEquiv π hπ m).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (node π (m + 2))
      (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 1)))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (AlgEquiv.symm_apply_eq (dvrMiddleReesEquiv π hπ m)).mpr
    (dvrMiddleReesEquiv_base π hπ m z).symm

@[reassoc] lemma rightChartMap_triangle (hπ : Irreducible π) :
    rightChartMap H hπ ≫ B.map = Spec.map (CommRingCat.ofHom (rightBase π m).toRingHom) := by
  rw [rightChartMap, Category.assoc, H.triangle]
  change Spec.map (CommRingCat.ofHom (dvrRightReesEquiv π hπ m).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (node π (m + 2))
      (affineBlowupAlgebra (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 2)))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (AlgEquiv.symm_apply_eq (dvrRightReesEquiv π hπ m)).mpr
    (dvrRightReesEquiv_base π hπ m z).symm


lemma three_charts_cover (hπ : Irreducible π) (y : B.Y) :
    y ∈ Set.range (leftChartMap H hπ) ∨
    y ∈ Set.range (middleChartMap H hπ) ∨
    y ∈ Set.range (rightChartMap H hπ) := by
  obtain ⟨i, hi⟩ := AlgebraicGeometry.Scheme.Blowup.AffineAtlas.generator_covers
    (generator π m) (generator_span π m) H y
  simp only [leftChartMap, middleChartMap, rightChartMap, range_iso_comp]
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

end AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas

end
end AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas

section AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps


/-!
# Literal scheme overlaps of the three-chart node blowup

The inverse images of the pairwise chart intersections are exactly D(P), D(S),
D(Q), D(T), and D(pi^m P^2). This includes m = 0. The transitions below are
actual scheme isomorphisms over the same blowup, derived from the affine atlas
and the proved ratio identities. No overlap or gluing premise is introduced.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup _root_.PowerNode.Rees
open PlaneNode AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
open AlgebraicGeometry.Scheme.Blowup.Coordinates
namespace AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π) (m : ℕ)

lemma left_middle_ratio : dvrLeftReesEquiv π hπ m (PlaneNode.V π) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 0) (generator π m 1) := by
  apply Subtype.ext
  change leftToLocalization π m (PlaneNode.V π) =
    algebraMap (node π (m + 2)) (leftLocalization π m) (algebraMap R _ π) * leftDenominator π m
  rw [leftToLocalization_v]
  change algebraMap R (leftLocalization π m) π * leftDenominator π m = _
  rw [IsScalarTower.algebraMap_apply R (node π (m + 2)) (leftLocalization π m)]

lemma middle_left_ratio : dvrMiddleReesEquiv π hπ m (PlaneNode.U (π^m)) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 1) (generator π m 0) := by
  apply Subtype.ext
  exact middleToLocalization_u π m

lemma right_middle_ratio : dvrRightReesEquiv π hπ m (PlaneNode.V π) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 2) (generator π m 1) := by
  apply Subtype.ext
  change rightToLocalization π m (PlaneNode.V π) =
    algebraMap (node π (m + 2)) (rightLocalization π m) (algebraMap R _ π) *
      IsLocalization.Away.invSelf (PlaneNode.V (π^(m + 2)))
  rw [rightToLocalization_v]
  change algebraMap R (rightLocalization π m) π * IsLocalization.Away.invSelf (PlaneNode.V (π^(m +
    2))) = _
  rw [IsScalarTower.algebraMap_apply R (node π (m + 2)) (rightLocalization π m)]

lemma middle_right_ratio : dvrMiddleReesEquiv π hπ m (PlaneNode.V (π^m)) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 1) (generator π m 2) := by
  apply Subtype.ext
  exact middleToLocalization_v π m

lemma left_right_ratio : dvrLeftReesEquiv π hπ m (outerRatio π m) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 0) (generator π m 2) := by
  apply Subtype.ext
  change leftToLocalization π m (outerRatio π m) =
    fraction (PlaneNode.U (π^(m + 2))) (PlaneNode.V (π^(m + 2)))
  simp only [outerRatio, map_mul, AlgHom.commutes, map_pow, leftToLocalization_v]
  simpa only [map_pow] using (left_ratio_v π m).symm

lemma right_left_ratio : dvrRightReesEquiv π hπ m (outerRatio π m) =
    ratio (node π (m + 2)) (centerIdeal π (m + 2)) (generator π m 2) (generator π m 0) := by
  apply Subtype.ext
  change rightToLocalization π m (outerRatio π m) =
    fraction (PlaneNode.V (π^(m + 2))) (PlaneNode.U (π^(m + 2)))
  simp only [outerRatio, map_mul, AlgHom.commutes, map_pow, rightToLocalization_v]
  simpa only [map_pow] using (right_ratio_u π m).symm

variable {π m}
variable {B : BlowupDatum (affineCenter (node π (m + 2)) (centerIdeal π (m + 2)))}
variable (H : AffineAtlas (node π (m + 2)) (centerIdeal π (m + 2)) B)

lemma left_middle_range : Set.range (awayMap (PlaneNode.V π) ≫ leftChartMap H hπ) =
    Set.range (leftChartMap H hπ) ∩ Set.range (middleChartMap H hπ) :=
  overlap_range H (generator π m 0) (generator π m 1)
    (dvrLeftReesEquiv π hπ m).toRingEquiv (dvrMiddleReesEquiv π hπ m).toRingEquiv
    (PlaneNode.V π) (left_middle_ratio π hπ m)

lemma right_middle_range : Set.range (awayMap (PlaneNode.V π) ≫ rightChartMap H hπ) =
    Set.range (rightChartMap H hπ) ∩ Set.range (middleChartMap H hπ) :=
  overlap_range H (generator π m 2) (generator π m 1)
    (dvrRightReesEquiv π hπ m).toRingEquiv (dvrMiddleReesEquiv π hπ m).toRingEquiv
    (PlaneNode.V π) (right_middle_ratio π hπ m)

lemma outer_range : Set.range (awayMap (outerRatio π m) ≫ leftChartMap H hπ) =
    Set.range (leftChartMap H hπ) ∩ Set.range (rightChartMap H hπ) :=
  overlap_range H (generator π m 0) (generator π m 2)
    (dvrLeftReesEquiv π hπ m).toRingEquiv (dvrRightReesEquiv π hπ m).toRingEquiv
    (outerRatio π m) (left_right_ratio π hπ m)

/-- D(P) on the outer u-chart is D(S) on the middle chart, over the blowup. -/
def leftMiddleIso : Spec (.of (leftOverlap π)) ≅ Spec (.of (middleLeftOverlap π m)) :=
  overlapIso H (generator π m 0) (generator π m 1)
    (dvrLeftReesEquiv π hπ m).toRingEquiv (dvrMiddleReesEquiv π hπ m).toRingEquiv
    (PlaneNode.V π) (PlaneNode.U (π^m)) (left_middle_ratio π hπ m) (middle_left_ratio π hπ m)

/-- D(Q) on the outer v-chart is D(T) on the middle chart, over the blowup. -/
def rightMiddleIso : Spec (.of (leftOverlap π)) ≅
    Spec (.of (Localization.Away (PlaneNode.V (π^m)))) :=
  overlapIso H (generator π m 2) (generator π m 1)
    (dvrRightReesEquiv π hπ m).toRingEquiv (dvrMiddleReesEquiv π hπ m).toRingEquiv
    (PlaneNode.V π) (PlaneNode.V (π^m)) (right_middle_ratio π hπ m) (middle_right_ratio π hπ m)

/-- The literal two outer-chart overlap rings, over the same blowup. -/
def outerIso : Spec (.of (outerOverlap π m)) ≅ Spec (.of (outerOverlap π m)) :=
  overlapIso H (generator π m 0) (generator π m 2)
    (dvrLeftReesEquiv π hπ m).toRingEquiv (dvrRightReesEquiv π hπ m).toRingEquiv
    (outerRatio π m) (outerRatio π m) (left_right_ratio π hπ m) (right_left_ratio π hπ m)

@[reassoc] lemma leftMiddleIso_hom_triangle :
    (leftMiddleIso hπ H).hom ≫ awayMap (PlaneNode.U (π^m)) ≫ middleChartMap H hπ =
      awayMap (PlaneNode.V π) ≫ leftChartMap H hπ :=
  overlapIso_hom_triangle ..
@[reassoc] lemma leftMiddleIso_inv_triangle :
    (leftMiddleIso hπ H).inv ≫ awayMap (PlaneNode.V π) ≫ leftChartMap H hπ =
      awayMap (PlaneNode.U (π^m)) ≫ middleChartMap H hπ :=
  overlapIso_inv_triangle ..
@[reassoc] lemma rightMiddleIso_hom_triangle :
    (rightMiddleIso hπ H).hom ≫ awayMap (PlaneNode.V (π^m)) ≫ middleChartMap H hπ =
      awayMap (PlaneNode.V π) ≫ rightChartMap H hπ :=
  overlapIso_hom_triangle ..
@[reassoc] lemma rightMiddleIso_inv_triangle :
    (rightMiddleIso hπ H).inv ≫ awayMap (PlaneNode.V π) ≫ rightChartMap H hπ =
      awayMap (PlaneNode.V (π^m)) ≫ middleChartMap H hπ :=
  overlapIso_inv_triangle ..
@[reassoc] lemma outerIso_hom_triangle :
    (outerIso hπ H).hom ≫ awayMap (outerRatio π m) ≫ rightChartMap H hπ =
      awayMap (outerRatio π m) ≫ leftChartMap H hπ :=
  overlapIso_hom_triangle ..
@[reassoc] lemma outerIso_inv_triangle :
    (outerIso hπ H).inv ≫ awayMap (outerRatio π m) ≫ leftChartMap H hπ =
      awayMap (outerRatio π m) ≫ rightChartMap H hπ :=
  overlapIso_inv_triangle ..

end AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps

end
end AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps

section AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup


/-!
# Conditional one-step proper blowup with a genuine finite affine atlas

The only retained independent general families are exactly
`NoetherianBlowupExistence`, `NoetherianBlowupProper`, and `BlowupAffineAtlas`.
They remain explicit unproved arguments. Finiteness, the three source rings,
all charts, covering, and all triangles are outputs of the preceding proofs.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup _root_.PowerNode.Rees
open PlaneNode AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
namespace AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (m : ℕ)

/-- A proper blowup of the exponent-`m + 2` node at its centre, equipped with an affine atlas. -/
structure Data where
  /-- The blowup datum for the centre ideal of the exponent-`m + 2` node. -/
  blowup : BlowupDatum (affineCenter (node π (m + 2)) (centerIdeal π (m + 2)))
  proper : IsProper blowup.map
  /-- The affine blowup atlas used to construct the three explicit node charts. -/
  atlas : AffineAtlas (node π (m + 2)) (centerIdeal π (m + 2)) blowup

/-- A selected actual blowup, conditional on the three displayed general
families. No family is silently asserted or instantiated globally. -/
def ofFamilies (hex : NoetherianBlowupExistence.{u})
    (hp : NoetherianBlowupProper.{u}) (ha : BlowupAffineAtlas.{u}) : Data π m := by
  let B := Classical.choice (hex (Spec (.of (node π (m + 2))))
    (affineCenter (node π (m + 2)) (centerIdeal π (m + 2))))
  exact ⟨B, hp _ _ B, Classical.choice (ha _ _ B)⟩

variable {π m} (D : Data π m) (hπ : Irreducible π)

/-- The coordinate ring of the left, middle, or right chart, indexed in that order. -/
def chartRing (i : Fin 3) : CommRingCat.{u} :=
  ![.of (PlaneNode.Ring π), .of (node π m), .of (PlaneNode.Ring π)] i

/-- The open chart map from the indexed node chart into the chosen blowup. -/
def chartMap : ∀ i : Fin 3, Spec (chartRing (π := π) (m := m) i) ⟶ D.blowup.Y
  | 0 => leftChartMap D.atlas hπ
  | 1 => middleChartMap D.atlas hπ
  | 2 => rightChartMap D.atlas hπ

instance chartMap_isOpenImmersion (i : Fin 3) : IsOpenImmersion (chartMap D hπ i) := by
  fin_cases i
  · exact BlowupAtlas.leftChartMap_isOpenImmersion D.atlas hπ
  · exact BlowupAtlas.middleChartMap_isOpenImmersion D.atlas hπ
  · exact BlowupAtlas.rightChartMap_isOpenImmersion D.atlas hπ

lemma chartMap_covers (y : D.blowup.Y) : ∃ i, y ∈ Set.range (chartMap D hπ i) := by
  obtain h | h | h := three_charts_cover D.atlas hπ y
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

/-- A literal finite affine open cover, indexed by precisely `Fin 3`. -/
def affineOpenCover : D.blowup.Y.AffineOpenCover where
  I₀ := Fin 3
  X := chartRing
  f := chartMap D hπ
  idx y := (chartMap_covers D hπ y).choose
  covers y := (chartMap_covers D hπ y).choose_spec

instance finite_cover_index : Finite (affineOpenCover D hπ).I₀ := by
  change Finite (Fin 3)
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The packaged structural map is the same ordinary proper blowup map. -/
theorem proper_blowdown : IsProper D.blowup.map := D.proper

end AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup

end
end AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup
