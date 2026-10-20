/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The genuine two-chart projective line over an affine base

Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/Charts.lean` at revision
`8273990b7977bd87edfe94cd2be91dec64de79aa`. The collision-free native owner
retains the same literal pushout, chart inclusions and structural projection.

This construction is the scheme pushout of the two original polynomial charts
along the Laurent chart, with inverse coordinate transition. Comparisons with
Proj, twisting sheaves, and projective pushforward are separate constructions.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- The actual gluing of the two affine-line charts by coordinate inversion. -/
def twoChartLine : AlgebraicGeometry.Scheme := pushout (laurentPlus R) (laurentMinus R)

/-- The original positive polynomial chart. -/
def plusChart : Spec (.of (Polynomial R)) ⟶ twoChartLine R := pushout.inl _ _

/-- The original negative polynomial chart. -/
def minusChart : Spec (.of (Polynomial R)) ⟶ twoChartLine R := pushout.inr _ _

instance : IsOpenImmersion (plusChart R) := by
  change IsOpenImmersion (colimit.ι (span (laurentPlus R) (laurentMinus R)) WalkingSpan.left)
  infer_instance

instance : IsOpenImmersion (minusChart R) := by
  change IsOpenImmersion (colimit.ι (span (laurentPlus R) (laurentMinus R)) WalkingSpan.right)
  infer_instance

/-- One of the two original polynomial charts, with `true` selecting the positive chart. -/
def polynomialChart (R : CommRingCat.{u}) (b : Bool) :
    Spec (.of (Polynomial R)) ⟶ twoChartLine R := if b then plusChart R else minusChart R

instance (R : CommRingCat.{u}) (b : Bool) : IsOpenImmersion (polynomialChart R b) := by
  cases b <;> dsimp [polynomialChart] <;> infer_instance

lemma overlap_equation : laurentPlus R ≫ plusChart R = laurentMinus R ≫ minusChart R :=
  pushout.condition

/-- The actual projection to the original affine base. -/
def projection : twoChartLine R ⟶ Spec R :=
  pushout.desc (polynomialProjection R) (polynomialProjection R)
    ((laurentPlus_projection R).trans (laurentMinus_projection R).symm)

@[reassoc (attr := simp)] lemma plusChart_projection :
    plusChart R ≫ projection R = polynomialProjection R := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma minusChart_projection :
    minusChart R ≫ projection R = polynomialProjection R := pushout.inr_desc _ _ _

/-- Each original chart lies over the actual polynomial projection. -/
theorem polynomialChart_projection (R : CommRingCat.{u}) (b : Bool) :
    polynomialChart R b ≫ projection R = polynomialProjection R := by
  cases b <;> simp [polynomialChart, plusChart_projection, minusChart_projection]

lemma charts_jointly_surjective (x : twoChartLine R) :
    (∃ a, plusChart R a = x) ∨ ∃ b, minusChart R b = x := by
  obtain ⟨i, y, hy⟩ := AlgebraicGeometry.Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (laurentPlus R) (laurentMinus R)) x
  cases i with
  | none =>
    refine Or.inl ⟨laurentPlus R y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact (congrArg (fun f => f y) (colimit.w (span (laurentPlus R) (laurentMinus R))
      WalkingSpan.Hom.fst)).trans hy
  | some i =>
    cases i with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

lemma chart_ranges_cover : (plusChart R).opensRange ⊔ (minusChart R).opensRange = ⊤ := by
  apply top_unique
  intro x _
  rcases charts_jointly_surjective R x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨b, rfl⟩

/-- The original Boolean chart family covers the actual projective line. -/
lemma polynomialChart_cover (x : twoChartLine R) :
    ∃ (b : Bool) (y : Spec (.of (Polynomial R))), polynomialChart R b y = x := by
  rcases charts_jointly_surjective R x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨true, y, hy⟩
  · exact ⟨false, y, hy⟩

/-- The chart identifications are exactly the original Laurent transition. -/
lemma chart_eq_iff (a b : Spec (.of (Polynomial R))) :
    plusChart R a = minusChart R b ↔
      ∃ z : Spec (.of (LaurentPolynomial R)), laurentPlus R z = a ∧ laurentMinus R z = b := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, z, ha, hb⟩ :=
      (AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff
        (span (laurentPlus R) (laurentMinus R))
        (i := WalkingSpan.left) (j := WalkingSpan.right)).mp h
    cases k with
    | none =>
      cases fi
      cases fj
      exact ⟨z, ha, hb⟩
    | some k =>
      cases k with
      | left => cases fj
      | right => cases fi
  · rintro ⟨z, rfl, rfl⟩
    exact congrArg (fun f => f z) (overlap_equation R)

lemma plusChart_preimage_minusRange :
    plusChart R ⁻¹ᵁ (minusChart R).opensRange = (laurentPlus R).opensRange := by
  ext a
  change (∃ b, minusChart R b = plusChart R a) ↔ ∃ z, laurentPlus R z = a
  constructor
  · rintro ⟨b, h⟩
    obtain ⟨z, hz, _⟩ := (chart_eq_iff R a b).mp h.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨laurentMinus R z, (congrArg (fun f => f z) (overlap_equation R)).symm⟩

/-- The original Laurent chart is the actual geometric intersection of the two charts. -/
lemma chart_isPullback :
    IsPullback (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R) :=
  (IsOpenImmersion.isPullback (laurentMinus R) (laurentPlus R)
    (minusChart R) (plusChart R) (overlap_equation R)
      (plusChart_preimage_minusRange R)).flip

instance : CompactSpace (twoChartLine R) := by
  let F := span (laurentPlus R) (laurentMinus R)
  have hF (i : WalkingSpan) : CompactSpace (F.obj i) := by
    cases i with
    | none => change CompactSpace (Spec (.of (LaurentPolynomial R))); infer_instance
    | some i => cases i <;> change CompactSpace (Spec (.of (Polynomial R))) <;> infer_instance
  have : Finite (AlgebraicGeometry.Scheme.IsLocallyDirected.openCover F).I₀ := by
    change Finite WalkingSpan
    infer_instance
  have (i : (AlgebraicGeometry.Scheme.IsLocallyDirected.openCover F).I₀) :
      CompactSpace ((AlgebraicGeometry.Scheme.IsLocallyDirected.openCover F).X i) := by
    change CompactSpace (F.obj i)
    exact hF i
  exact (AlgebraicGeometry.Scheme.IsLocallyDirected.openCover F).compactSpace

lemma chart_ranges_inter :
    (plusChart R).opensRange ⊓ (minusChart R).opensRange =
      (laurentPlus R ≫ plusChart R).opensRange := by
  ext x
  change ((∃ a, plusChart R a = x) ∧ (∃ b, minusChart R b = x)) ↔
    ∃ z, (laurentPlus R ≫ plusChart R) z = x
  constructor
  · rintro ⟨⟨a, ha⟩,⟨b, hb⟩⟩
    obtain ⟨z, hz, _⟩ := (chart_eq_iff R a b).mp (ha.trans hb.symm)
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, ha]⟩
  · rintro ⟨z, rfl⟩
    refine ⟨⟨laurentPlus R z, rfl⟩,⟨laurentMinus R z, ?_⟩⟩
    exact (congrArg (fun f => f z) (overlap_equation R)).symm

instance : QuasiSeparatedSpace (twoChartLine R) := by
  let U : Bool → (twoChartLine R).Opens := fun b =>
    if b then (plusChart R).opensRange else (minusChart R).opensRange
  have hU : TopologicalSpace.IsOpenCover U := by
    simpa only [TopologicalSpace.IsOpenCover, iSup_bool_eq, U, Bool.false_eq_true,
      ite_false, ite_true, sup_comm] using chart_ranges_cover R
  have hp : IsCompact ((plusChart R).opensRange : Set (twoChartLine R)) :=
    isCompact_range (plusChart R).continuous
  have hm : IsCompact ((minusChart R).opensRange : Set (twoChartLine R)) :=
    isCompact_range (minusChart R).continuous
  have hpm : IsCompact (((plusChart R).opensRange ⊓ (minusChart R).opensRange) :
      Set (twoChartLine R)) := by
    have h := isCompact_range (laurentPlus R ≫ plusChart R).continuous
    convert h using 1
    exact congrArg (fun V : (twoChartLine R).Opens => (V : Set (twoChartLine R)))
      (chart_ranges_inter R)
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U hU ?_ ?_
  · intro b
    cases b <;> exact isAffineOpen_opensRange _
  · intro b c
    cases b <;> cases c
    · simpa [U] using hm
    · simpa [U, Set.inter_comm] using hpm
    · simpa [U] using hpm
    · simpa [U] using hp

instance instFlatProjection : Flat (projection R) := by
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let F := span (laurentPlus R) (laurentMinus R)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat.{u}) (f := projection R)
    (AlgebraicGeometry.Scheme.IsLocallyDirected.openCover F)).mpr ?_
  intro i
  change Flat (colimit.ι F i ≫ projection R)
  cases i with
  | none =>
    rw [← colimit.w F WalkingSpan.Hom.fst]
    change Flat ((laurentPlus R ≫ plusChart R) ≫ projection R)
    rw [Category.assoc, plusChart_projection, laurentPlus_projection]
    infer_instance
  | some i =>
    cases i with
    | left => change Flat (plusChart R ≫ projection R); rw [plusChart_projection]; infer_instance
    | right => change Flat (minusChart R ≫ projection R); rw [minusChart_projection]; infer_instance

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
