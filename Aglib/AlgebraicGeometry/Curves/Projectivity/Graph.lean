/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.RingTheory.Polynomial.GraphRelations
public import Aglib.AlgebraicGeometry.Limits.Polynomial
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Aglib.AlgebraicGeometry.Morphisms.Surjective.GenericPoint
public import Aglib.AlgebraicGeometry.RationalMap.Graph
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.PolynomialCharts
public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Geometric finite graph models for proper field curves

The actual affine section, two-chart line and integral rational graph construction
retain the original fields, structural arrows and dimension conditions. Generic
proper-dominant dimension-one finiteness is owned by `Scheme.DimensionOne`.
This is the pure geometry slice, lines 167–662, of
`R5Lab.Aglib.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness` at R5Lab
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The older Laurent H1 chain is
not a prerequisite of these declarations.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Pullback.Polynomial

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve.GraphInput
variable {K : Type u} [Field K]

/-- A positive-dimensional integral field scheme has an actual affine section
which is nonzero and not a unit. -/
theorem exists_affine_nonzero_nonunit (X : FScheme K)
    [IsIntegral X.left]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ U : X.left.affineOpens, Nonempty U.1 ∧
      ∃ a : Γ(X.left, U.1), a ≠ 0 ∧ ¬ IsUnit a := by
  have hnss : ¬ Subsingleton X.left := by
    intro h
    let := h
    have hle := topologicalKrullDim_zero_of_discreteTopology X.left
    rw [hdim] at hle
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hle
  let : Nontrivial X.left := not_subsingleton_iff_nontrivial.mp hnss
  obtain ⟨x, hx⟩ := exists_ne (genericPoint X.left)
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (U := ⊤) (x := x) (by trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨⟨U, hU⟩, inferInstance, ?_⟩
  suffices hnfield : ¬ IsField Γ(X.left, U) by
    obtain ⟨a, ha0, haunit⟩ := Ring.exists_not_isUnit_of_not_isField hnfield
    exact ⟨a, ha0, haunit⟩
  intro hfield
  let : Field Γ(X.left, U) := hfield.toField
  let : Subsingleton (Spec Γ(X.left, U)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Γ(X.left, U)))
  have hUss : Subsingleton U :=
    Function.Injective.subsingleton hU.isoSpec.hom.homeomorph.injective
  have hηU : genericPoint X.left ∈ U :=
    (genericPoint_specializes x).mem_open U.isOpen hxU
  have hηx : genericPoint X.left = x :=
    congrArg Subtype.val (hUss.elim ⟨_, hηU⟩ ⟨_, hxU⟩)
  exact hx hηx.symm

/-- The actual affine section can be chosen transcendental for the structural
constant map. No rational-function replacement is used. -/
theorem exists_affine_transcendental (X : FScheme K)
    [IsIntegral X.left]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ U : X.left.affineOpens, Nonempty U.1 ∧
      ∃ a : Γ(X.left, U.1),
        letI := (constantSection X U.1).toAlgebra
        Transcendental K a := by
  obtain ⟨U, hU, a, ha0, haunit⟩ := exists_affine_nonzero_nonunit X hdim
  let : Nonempty U.1 := hU
  let := (constantSection X U.1).toAlgebra
  exact ⟨U, hU, a, fun ha => haunit (ha.isIntegral.isUnit ha0)⟩

/-- Shrinking to the principal open makes the actual transcendental section a
unit, while restriction remains injective on an integral scheme. -/
theorem exists_affine_transcendental_unit (X : FScheme K)
    [IsIntegral X.left]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ U : X.left.affineOpens, Nonempty U.1 ∧
      ∃ a : Γ(X.left, U.1),
        letI := (constantSection X U.1).toAlgebra
        Transcendental K a ∧ IsUnit a := by
  obtain ⟨U, hU, a, ha⟩ := exists_affine_transcendental X hdim
  let : Nonempty U.1 := hU
  let := (constantSection X U.1).toAlgebra
  let V := X.left.basicOpen a
  have ha0 : a ≠ 0 := fun h => ha (h ▸ isAlgebraic_zero)
  have hV : (V : Set X.left).Nonempty := by
    by_contra h
    exact ha0 ((basicOpen_eq_bot_iff a).mp ((Opens.not_nonempty_iff_eq_bot V).mp h))
  let : Nonempty V := hV.to_subtype
  let i : V ⟶ U.1 := homOfLE (X.left.basicOpen_le a)
  let r : Γ(X.left, U.1) →+* Γ(X.left, V) := (X.left.presheaf.map i.op).hom
  let := (constantSection X V).toAlgebra
  refine ⟨⟨V, U.2.basicOpen a⟩, inferInstance, r a, ?_, ?_⟩
  · apply ha.ringHom_of_comp_eq (RingHom.id K) r Function.surjective_id
      (map_injective_of_isIntegral X.left i)
    ext c
    exact (map_constantSection X i c).symm
  · exact X.left.toRingedSpace.isUnit_res_basicOpen a

end AlgebraicGeometry.Scheme.OverField.Curve.GraphInput
end

/- Component: ChartDimension; declaration bodies preserved. -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u v

/-- The literal affine polynomial chart over a field has dimension one. -/
theorem polynomialChart_topologicalKrullDim (K : Type u) [Field K] :
    topologicalKrullDim (Spec (.of (Polynomial K))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial K)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- The original two-chart projective line over any field has dimension exactly one. -/
theorem twoChartLine_topologicalKrullDim (K : Type u) [Field K] :
    topologicalKrullDim (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.twoChartLine (.of
      K)) = 1 := by
  let 𝒰 : Scheme.OpenCover (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.twoChartLine
    (.of K)) :=
    Scheme.Cover.mkOfCovers Bool (fun _ => Spec (.of (Polynomial K)))
      (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.polynomialChart (.of K))
      (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.polynomialChart_cover (.of K))
      (fun _ => inferInstance)
  apply le_antisymm
  · exact topologicalKrullDim_le_of_openCover 𝒰 1
      (fun _ => (polynomialChart_topologicalKrullDim K).le)
  · rw [← polynomialChart_topologicalKrullDim K]
    exact (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart (.of
      K)).isOpenEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end

/- Component: ProperDominantFinite; declaration bodies preserved. -/
/-!
Finite proper dominant maps from integral Noetherian curves.
This file uses only geometric and topological inputs. In particular it uses no
cohomology theorem, graph-construction premise, projectivity, smoothness,
normality, or perfection of a ground field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order Set

namespace AlgebraicGeometry.Scheme.DimensionOne
universe u

attribute [local instance] specializationOrder in
/-- Every nongeneric point of an irreducible scheme of dimension at most one is closed. -/
theorem point_eq_generic_or_isClosed (X : Scheme.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    x = genericPoint X ∨ IsClosed ({x} : Set X) := by
  have hd : krullDim X ≤ 1 := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  rcases krullDim_le_one_iff.mp hd x with hx | hx
  · right
    rw [← closure_eq_iff_isClosed]
    apply Set.Subset.antisymm
    · intro y hy
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have he : x = y := le_antisymm (hx hxy) hxy
      exact he ▸ Set.mem_singleton x
    · exact subset_closure
  · left
    exact le_antisymm (genericPoint_specializes x) (hx (genericPoint_specializes x))

attribute [local instance] specializationOrder in
/-- A proper closed subset of an irreducible Noetherian curve is finite. -/
theorem finite_of_isClosed_of_ne_univ (X : Scheme.{u}) [IrreducibleSpace X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hne : Z ≠ Set.univ) : Z.Finite := by
  have hd : krullDim X ≤ 1 := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  let : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hn : closure Z ≠ Set.univ := by rwa [hZ.closure_eq]
  apply (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hn).subset
  intro x hx
  refine ⟨hx, le_antisymm ?_ ?_⟩
  · exact WithBot.coe_le_coe.mp ((coheight_le_krullDim x).trans hd)
  · apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have hm := coheight_eq_zero.mp hz
    have hgen : x = genericPoint X :=
      le_antisymm (genericPoint_specializes x) (hm (genericPoint_specializes x))
    have hsub : closure ({genericPoint X} : Set X) ⊆ Z :=
      hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (hgen ▸ hx))
    rw [genericPoint_closure] at hsub
    exact hne (Set.eq_univ_of_univ_subset hsub)

/-- Dimension one excludes a closed generic point. -/
theorem genericPoint_not_isClosed_of_dimension_one (X : Scheme.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 1) : ¬ IsClosed ({genericPoint X} : Set X) := by
  intro hc
  have heq (x : X) : x = genericPoint X := by
    have hx := specializes_iff_mem_closure.mp (genericPoint_specializes x)
    rwa [hc.closure_eq, Set.mem_singleton_iff] at hx
  let : Subsingleton X := ⟨fun x y => (heq x).trans (heq y).symm⟩
  have hzero := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hzero

/-- Proper dominant maps from irreducible Noetherian curves to an irreducible
scheme with nonclosed generic point have finite set-theoretic fibers. -/
theorem finite_preimage_singleton (Y X : Scheme.{u}) [IrreducibleSpace Y]
    [NoetherianSpace Y] [IrreducibleSpace X] (f : Y ⟶ X)
    [IsProper f] [IsDominant f] (hdim : topologicalKrullDim Y ≤ 1)
    (hgeneric : ¬ IsClosed ({genericPoint X} : Set X)) (x : X) :
    (f ⁻¹' {x}).Finite := by
  classical
  have hg := Scheme.map_genericPoint_of_surjective Y X f
  by_cases hx : x = genericPoint X
  · apply (Set.finite_singleton (genericPoint Y)).subset
    intro y hy
    have hyx : f y = x := hy
    rcases point_eq_generic_or_isClosed Y hdim y with h | h
    · exact h
    · have hc : IsClosed ({genericPoint X} : Set X) := by
        simpa only [Set.image_singleton, hyx, hx] using f.isClosedMap _ h
      exact (hgeneric hc).elim
  · have hc : IsClosed (f ⁻¹' closure ({x} : Set X)) :=
      isClosed_closure.preimage f.continuous
    have hn : f ⁻¹' closure ({x} : Set X) ≠ Set.univ := by
      intro he
      have hm : f (genericPoint Y) ∈ closure ({x} : Set X) := by
        change genericPoint Y ∈ f ⁻¹' closure ({x} : Set X)
        rw [he]
        exact Set.mem_univ _
      rw [hg] at hm
      have hsp : x ⤳ genericPoint X := specializes_iff_mem_closure.mpr hm
      exact hx (hsp.antisymm (genericPoint_specializes x)).eq
    exact (finite_of_isClosed_of_ne_univ Y hdim hc hn).subset
      (Set.preimage_mono subset_closure)

/-- A proper dominant morphism from an irreducible Noetherian curve to an
irreducible scheme with nonclosed generic point is finite. -/
theorem isFinite_of_isProper_of_isDominant (Y X : Scheme.{u}) [IrreducibleSpace Y]
    [NoetherianSpace Y] [IrreducibleSpace X] (f : Y ⟶ X)
    [IsProper f] [IsDominant f] (hdim : topologicalKrullDim Y ≤ 1)
    (hgeneric : ¬ IsClosed ({genericPoint X} : Set X)) : IsFinite f := by
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (finite_preimage_singleton Y X f hdim hgeneric)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- The dimension-one-target form used by both projections of the rational graph. -/
theorem isFinite_of_isProper_of_isDominant_of_dimension_one
    (Y X : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y] [IsIntegral X]
    (f : Y ⟶ X) [IsProper f] [IsDominant f]
    (hY : topologicalKrullDim Y ≤ 1) (hX : topologicalKrullDim X = 1) : IsFinite f :=
  isFinite_of_isProper_of_isDominant Y X f hY
    (genericPoint_not_isClosed_of_dimension_one X hX)

end AlgebraicGeometry.Scheme.DimensionOne

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u

/-- Proper dominant morphisms from integral Noetherian curves to integral
one-dimensional schemes are finite. No assumption on global sections or
cohomology is used. -/
theorem proper_dominant_curve_isFinite {Y X : Scheme.{u}}
    [IsIntegral Y] [IsNoetherian Y] [IsIntegral X]
    (f : Y ⟶ X) [IsProper f] [IsDominant f]
    (hY : topologicalKrullDim Y ≤ 1) (hX : topologicalKrullDim X = 1) : IsFinite f :=
  DimensionOne.isFinite_of_isProper_of_isDominant_of_dimension_one Y X f hY hX

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end

/- Component: RationalCoordinate; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u
variable {K : Type u} [Field K]

instance twoChartLine_isIntegral : IsIntegral (twoChartLine (.of K)) := by
  let C := AlgebraicGeometry.Scheme.OpenNormalizationGluing.twoChartCover
    (laurentPlus (.of K)) (laurentMinus (.of K))
  let (i : C.I₀) : IsReduced (C.X i) := by
    cases i <;>
      dsimp [C, AlgebraicGeometry.Scheme.OpenNormalizationGluing.twoChartCover] <;>
      infer_instance
  let : IsReduced (twoChartLine (.of K)) := IsReduced.of_openCover _ C
  have hd : DenseRange (plusChart (.of K)) := by
    have hm : DenseRange (laurentMinus (.of K)) :=
      (laurentMinus (.of K)).isOpenMap.denseRange_of_isPreirreducibleSpace
    intro z
    rcases Scheme.ProjectiveLine.TwoChart.charts_jointly_surjective (.of K) z with
      ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact subset_closure ⟨x, rfl⟩
    · refine hm.induction_on
        (p := fun v => minusChart (.of K) v ∈ closure (Set.range (plusChart (.of K))))
        y (isClosed_closure.preimage (minusChart (.of K)).continuous) ?_
      intro w
      rw [← Scheme.Hom.comp_apply, ← Scheme.ProjectiveLine.TwoChart.overlap_equation,
        Scheme.Hom.comp_apply]
      exact subset_closure ⟨laurentPlus (.of K) w, rfl⟩
  let : IrreducibleSpace (twoChartLine (.of K)) := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set (twoChartLine (.of K)))
    have hi : IsIrreducible (Set.range (plusChart (.of K))) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ (Spec (.of K[X]))).image _
          (plusChart (.of K)).continuous.continuousOn
    simpa only [hd.closure_range] using hi.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance plusChart_isDominant : IsDominant (plusChart (.of K)) :=
  ⟨(plusChart (.of K)).isOpenMap.denseRange_of_isPreirreducibleSpace⟩

/-- The original affine section defines a map to the original positive chart. -/
def affineSectionToLine (X : FScheme K) (U : X.left.affineOpens) (a : Γ(X.left, U.1)) :
    U.1.toScheme ⟶ twoChartLine (.of K) :=
  U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (constantSection X U.1)
    a)) ≫
    plusChart (.of K)

theorem affineSectionToLine_over (X : FScheme K) (U : X.left.affineOpens)
    (a : Γ(X.left, U.1)) :
    U.1.ι ≫ X.hom = affineSectionToLine X U a ≫ projection (.of K) := by
  rw [affineSectionToLine, Category.assoc, Category.assoc, plusChart_projection]
  unfold polynomialProjection
  rw [← Spec.map_comp]
  have h : (CommRingCat.ofHom (Polynomial.C : K →+* K[X])) ≫
      CommRingCat.ofHom (Polynomial.eval₂RingHom (constantSection X U.1) a) =
      CommRingCat.ofHom (constantSection X U.1) := by
    ext x; simp
  rw [h, ← affineOpen_fromSpec_over, ← Category.assoc]
  simp

theorem affineSectionToLine_isDominant (X : FScheme K) (U : X.left.affineOpens)
    (a : Γ(X.left, U.1))
    (ha : letI := (constantSection X U.1).toAlgebra; Transcendental K a) :
    IsDominant (affineSectionToLine X U a) := by
  let := (constantSection X U.1).toAlgebra
  let φ := Polynomial.eval₂RingHom (constantSection X U.1) a
  have hinj : Function.Injective φ := transcendental_iff_injective.mp ha
  let : IsDominant (Spec.map (CommRingCat.ofHom φ)) := ⟨by
    change DenseRange (PrimeSpectrum.comap φ)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hinj]
    exact bot_le⟩
  unfold affineSectionToLine
  infer_instance
end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end

/- Component: GraphExistence; declaration bodies preserved. -/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u
variable {K : Type u} [Field K]

/-- An actual integral proper curve admits an actual integral graph closure with
proper dominant projections and an isomorphism over a nonempty affine open.
Finiteness of the projections is a separate dimension-theoretic step. -/
theorem exists_proper_dominant_graph (X : FScheme K)
    [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ (U : X.left.affineOpens), Nonempty U.1 ∧
      ∃ (r : U.1.toScheme ⟶ twoChartLine (.of K))
        (hr : U.1.ι ≫ X.hom = r ≫ projection (.of K)),
        let P : FScheme K := Over.mk (projection (.of K))
        IsIntegral (rationalGraphImage X P U.1 r hr).left ∧
        IsNoetherian (rationalGraphImage X P U.1 r hr).left ∧
        IsProper (rationalGraphProjectionLeft X P U.1 r hr).left ∧
        IsProper (rationalGraphProjectionRight X P U.1 r hr).left ∧
        IsDominant (rationalGraphProjectionLeft X P U.1 r hr).left ∧
        IsDominant (rationalGraphProjectionRight X P U.1 r hr).left ∧
        IsIso ((rationalGraphProjectionLeft X P U.1 r hr).left ∣_ U.1) := by
  obtain ⟨U, hU, a, ha, _⟩ := GraphInput.exists_affine_transcendental_unit X hdim
  let : IsProper (Over.mk (projection (.of K)) : FScheme K).hom :=
    inferInstanceAs (IsProper (projection (.of K)))
  let : Nonempty U.1 := hU
  let r := affineSectionToLine X U a
  let hr := affineSectionToLine_over X U a
  let : IsDominant r := affineSectionToLine_isDominant X U a ha
  exact ⟨U, hU, r, hr, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end

/- Component: AmbientCharts; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u
variable {K : Type u} [Field K] (X : FScheme K)

/-- The two polynomial affine charts covering the glued projective line. -/
def graphLineOpenCover : (twoChartLine (.of K)).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun _ => Spec (.of K[X]))
    (polynomialChart (.of K)) (polynomialChart_cover (.of K)) (fun _ => inferInstance)

/-- The product open cover formed from affine opens of `X` and the two polynomial charts of the
line. -/
def graphProductOpenCover : (pullback X.hom (projection (.of K))).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (graphBaseOpenCover X)
    (graphLineOpenCover (K := K)) X.hom (projection (.of K))

/-- The isomorphism identifying a product-cover chart with the spectrum of a polynomial ring
over its affine-open section ring. -/
def graphProductChartIso (V : X.left.affineOpens) (b : Bool) :
    (graphProductOpenCover X).X (V, b) ≅ Spec (.of Γ(X.left, V.1)[X]) :=
  (pullback.congrHom rfl (polynomialChart_projection (.of K) b)) ≪≫
    affineOpenPolynomialPullbackIso X V.1 V.2

/-- The open chart of the product obtained from an affine open of `X` and one polynomial chart
of the line. -/
def graphProductChart (V : X.left.affineOpens) (b : Bool) :
    Spec (.of Γ(X.left, V.1)[X]) ⟶ pullback X.hom (projection (.of K)) :=
  (graphProductChartIso X V b).inv ≫ (graphProductOpenCover X).f (V, b)

instance graphProductChart_isOpenImmersion (V : X.left.affineOpens) (b : Bool) :
    IsOpenImmersion (graphProductChart X V b) := by
  unfold graphProductChart
  infer_instance

@[reassoc (attr := simp)]
theorem graphProductChart_fst (V : X.left.affineOpens) (b : Bool) :
    graphProductChart X V b ≫ pullback.fst X.hom (projection (.of K)) =
      Spec.map (CommRingCat.ofHom (C : Γ(X.left, V.1) →+* Γ(X.left, V.1)[X])) ≫
        V.2.fromSpec := by
  simp [graphProductChart, graphProductChartIso, graphProductOpenCover,
    graphBaseOpenCover, graphLineOpenCover, pullback.congrHom_inv, polynomialProjection]

@[reassoc (attr := simp)]
theorem graphProductChart_snd (V : X.left.affineOpens) (b : Bool) :
    graphProductChart X V b ≫ pullback.snd X.hom (projection (.of K)) =
      Spec.map (CommRingCat.ofHom (mapRingHom (constantSection X V.1))) ≫
        polynomialChart (.of K) b := by
  simp [graphProductChart, graphProductChartIso, graphProductOpenCover,
    graphBaseOpenCover, graphLineOpenCover, pullback.congrHom_inv, polynomialProjection]

theorem graphProductChart_cover (z : (pullback X.hom (projection (.of K)) : Scheme)) :
    ∃ (V : X.left.affineOpens) (b : Bool) (y : Spec (.of Γ(X.left, V.1)[X])),
      graphProductChart X V b y = z := by
  obtain ⟨⟨V, b⟩, y, rfl⟩ := (graphProductOpenCover X).exists_eq z
  refine ⟨V, b, (graphProductChartIso X V b).hom y, ?_⟩
  simp [graphProductChart, ← Scheme.Hom.comp_apply]

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end

/- Component: GraphDimension; declaration bodies preserved. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
universe u
variable {K : Type u} [Field K]

/-- The actual graph image has dimension at most one, proved on the original
polynomial product charts by a nonzero cleared-denominator relation. -/
theorem rationalGraphImage_dimension_le_one (X : FScheme K)
    [IsIntegral X.left] [IsNoetherian X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (U : X.left.Opens) (r : U.toScheme ⟶ twoChartLine (.of K))
    (hr : U.ι ≫ X.hom = r ≫ projection (.of K)) :
    topologicalKrullDim (rationalGraphImage X (Over.mk (projection (.of K))) U r hr).left ≤ 1 := by
  let P : FScheme K := Over.mk (projection (.of K))
  let g := rationalGraph X P U r hr
  let I := {V : X.left.affineOpens // Nonempty V.1} × Bool
  let W : I → g.image.Opens := fun i =>
    g.imageι ⁻¹ᵁ (graphProductChart X i.1.val i.2 ''ᵁ ⊤)
  have hcover : iSup W = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨V, b, z, hz⟩ := graphProductChart_cover X (g.imageι y)
    have hV : Nonempty V.1 :=
      ⟨V.2.isoSpec.inv ((Spec.map (CommRingCat.ofHom
        (C : Γ(X.left,V.1) →+* Γ(X.left,V.1)[X]))) z)⟩
    apply Opens.mem_iSup.mpr
    exact ⟨(⟨V, hV⟩, b), z, by trivial, hz⟩
  let 𝒰 := g.image.openCoverOfIsOpenCover W hcover
  apply topologicalKrullDim_le_of_openCover 𝒰 1
  rintro ⟨⟨V, hV⟩, b⟩
  let : Nonempty V.1 := hV
  let A := Γ(X.left,V.1)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian V
  let j := graphProductChart X V b
  have hA : ringKrullDim A ≤ 1 := by
    calc
      ringKrullDim A = topologicalKrullDim (Spec (.of A)) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).symm
      _ = topologicalKrullDim V.1.toScheme :=
        (IsHomeomorph.topologicalKrullDim_eq _ V.2.isoSpec.hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim X.left := V.1.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
      _ ≤ 1 := hdim
  obtain ⟨q, hq, hgq⟩ := graphChart_exists_nonzero_relation V.1 V.2 U.ι g
    (pullback.fst X.hom (projection (.of K)))
    (rationalGraph_fst X P U r hr) j (graphProductChart_fst X V b)
  have hR := graphImage_chart_ringKrullDim_le_one g A j hA hq hgq
  have hj : IsAffineOpen (j ''ᵁ ⊤) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange j
  have hW : IsAffineOpen (g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) := hj.preimage g.imageι
  change topologicalKrullDim (g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)).toScheme ≤ 1
  calc
    _ = topologicalKrullDim (Spec Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤))) :=
      IsHomeomorph.topologicalKrullDim_eq _ hW.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(g.image, g.imageι ⁻¹ᵁ (j ''ᵁ ⊤)) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ 1 := hR
end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
end
