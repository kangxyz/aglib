/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Intersections
public import Aglib.AlgebraicGeometry.Curves.FiniteEtaleGenusZero
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Geometry
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.PointComponent
public import Aglib.AlgebraicGeometry.RationalPoint.ClosedLift
public import Aglib.AlgebraicGeometry.Limits.OpenChartInjectivity
public import Aglib.Topology.Connected.FiniteClosedCover

/-!
# Actual normalization components of finite étale polygon covers

Same-field points lift through the actual finite normalization and every selected pullback. The
actual connected cover components propagate rationality through the original conductor nodes,
including both branches of the one-gon. Genus-zero triviality retains the original Riemann–Hurwitz
theorem-family premises; the unrestricted legacy pointed criterion and cohomology inputs are
discharged only by the proved applicable native suppliers. Source492–554 reuses the exact native
Intersections declarations.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/Cyclic/Covers/Components.lean`: source ranges [[164, 1127]];
SHA-256 `593810951171d1f9d65135289e94a3a63ca57073cfb37055f5afd0cdb7f3a5aa`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.RationalPoint AlgebraicGeometry.Scheme.Hom
open scoped Polynomial
universe u

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

/- Exact source prerequisite: FactorMaps.lean297–325, SHA-256
db0f255d82cc1322ebeb83e9b27c126483abb5c68d77c3879af0bcc49cca0173. -/
/-- The literal normalized-component composite retains the actual original-field structure. -/
@[reassoc] theorem componentParameter_over (i : Fin m) :
    componentLine k m i ≫ gluedPolynomialCover k m ≫ structureMap k m =
      Scheme.PinchedLine.lineStructure k := componentTarget_over k m i

private theorem normalizationRingMap_lift (K : Type u) [Field K]
    (f : nodeRing k m →+* K) :
    ∃ g : NormalizationRing k m →+* K, g.comp (nodeRing k m).val.toRingHom = f := by
  by_cases h : f (conductor k m) = 0
  · let p : nodeScheme k m := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
    obtain ⟨i, hi⟩ := nodePoint_exhaustive k m p h
    have hk : RingHom.ker (nodeValue k m i) ≤ RingHom.ker f := by
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal hi)
    let a : k →+* K := (nodeValue k m i).liftOfSurjective (nodeValue_surjective k m i) ⟨f, hk⟩
    refine ⟨(a.comp (Polynomial.evalRingHom 1)).comp (Pi.evalRingHom _ i), ?_⟩
    exact (nodeValue k m i).liftOfSurjective_comp (nodeValue_surjective k m i) ⟨f, hk⟩
  · let f' : nodeOverlapRing k m →+* K :=
      IsLocalization.Away.lift (conductor k m) (isUnit_iff_ne_zero.mpr h)
    let g : NormalizationRing k m →+* K :=
      (f'.comp (nodeProductOverlapEquiv k m).symm.toRingHom).comp
        (algebraMap (NormalizationRing k m) (productOverlapRing k m))
    refine ⟨g, ?_⟩
    apply RingHom.ext
    intro a
    change f' ((nodeProductOverlapEquiv k m).symm
      (algebraMap (NormalizationRing k m) (productOverlapRing k m) a.val)) = f a
    have he : (nodeProductOverlapEquiv k m).symm
        (algebraMap (NormalizationRing k m) (productOverlapRing k m) a.val) =
        algebraMap (nodeRing k m) (nodeOverlapRing k m) a := by
      apply (nodeProductOverlapEquiv k m).injective
      rw [RingEquiv.apply_symm_apply, nodeProductOverlapEquiv_algebraMap]
    rw [he]
    exact IsLocalization.Away.lift_eq _ _ a


/-- Every field-valued point lifts through the actual affine normalization map. -/
theorem polynomialCover_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ nodeScheme k m) :
    ∃ s : Spec (.of K) ⟶ Spec (.of (NormalizationRing k m)),
      s ≫ polynomialCover k m = p := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective p
  obtain ⟨g, hg⟩ := normalizationRingMap_lift k m K f.hom
  refine ⟨Spec.map (CommRingCat.ofHom g), ?_⟩
  rw [polynomialCover, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext hg

/-- The actual finite normalization of a split polygon lifts every field-valued
point over the SAME field, including all actual conductor nodes. -/
theorem gluedPolynomialCover_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ cycleScheme k m) :
    ∃ s : Spec (.of K) ⟶ normalizedScheme k m, s ≫ gluedPolynomialCover k m = p := by
  rcases Scheme.openPushout_covered (gluingToNode k m) (gluingToInfinity k m)
      (p (IsLocalRing.closedPoint K)) with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hr : Set.range p ⊆ Set.range (pushout.inl (gluingToNode k m) (gluingToInfinity k m)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨a, by rwa [hx]⟩
    let q := IsOpenImmersion.lift (pushout.inl (gluingToNode k m) (gluingToInfinity k m)) p hr
    obtain ⟨s, hs⟩ := polynomialCover_fieldPoint_lift k m K q
    refine ⟨s ≫ pushout.inl (normalizationOverlapInclusion k m) (gluingToInfinity k m), ?_⟩
    rw [Category.assoc, gluedPolynomialCover, Scheme.OpenNormalizationGluing.affine_chart,
      ← Category.assoc, hs]
    exact IsOpenImmersion.lift_fac _ _ hr
  · have hr : Set.range p ⊆ Set.range (pushout.inr (gluingToNode k m) (gluingToInfinity k m)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨a, by rwa [hx]⟩
    let q := IsOpenImmersion.lift (pushout.inr (gluingToNode k m) (gluingToInfinity k m)) p hr
    refine ⟨q ≫ pushout.inr (normalizationOverlapInclusion k m) (gluingToInfinity k m), ?_⟩
    rw [Category.assoc, gluedPolynomialCover, Scheme.OpenNormalizationGluing.infinity_chart]
    exact IsOpenImmersion.lift_fac _ _ hr

/-- Every field-valued point lifts through one of the ACTUAL normalized P1
component morphisms, with no supplied component index or branch. -/
theorem componentLine_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ cycleScheme k m) :
    ∃ (i : Fin m) (s : Spec (.of K) ⟶ Scheme.PinchedLine.lineGluing k),
      s ≫ componentLine k m i ≫ gluedPolynomialCover k m = p := by
  obtain ⟨q, hq⟩ := gluedPolynomialCover_fieldPoint_lift k m K p
  obtain ⟨⟨i⟩, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun _ : Fin m => Scheme.PinchedLine.lineGluing k))
    ((normalizationLinesIso k m).hom (q default))
  change Sigma.ι (fun _ : Fin m => Scheme.PinchedLine.lineGluing k) i a = _ at ha
  have ha' : componentLine k m i a = q default := by
    apply (normalizationLinesIso k m).hom.homeomorph.injective
    calc
      (normalizationLinesIso k m).hom (componentLine k m i a) =
          Sigma.ι (fun _ : Fin m => Scheme.PinchedLine.lineGluing k) i a :=
        congrArg (fun t => t a) (componentLine_toLines k m i)
      _ = _ := ha
  have hr : Set.range q ⊆ Set.range (componentLine k m i) := by
    rintro _ ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    exact ⟨a, by rwa [hx]⟩
  refine ⟨i, IsOpenImmersion.lift (componentLine k m i) q hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact hq

variable {Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m)

/-- The literal pullback of an arbitrary source along the actual normal source. -/
abbrev normalizedPullback : Scheme.{u} := pullback (gluedPolynomialCover k m) f

/-- The projection to the arbitrary original source is finite and surjective. -/
instance normalizedPullback_projection_finite :
    IsFinite (pullback.snd (gluedPolynomialCover k m) f) := inferInstance
/-- Surjectivity is preserved by this actual normalization base change. -/
instance normalizedPullback_projection_surjective :
    Surjective (pullback.snd (gluedPolynomialCover k m) f) := inferInstance

/-- For an arbitrary actual finite étale cover, its other projection is finite étale. -/
instance normalizedPullback_toNormal_finite [IsFinite f] :
    IsFinite (pullback.fst (gluedPolynomialCover k m) f) := inferInstance
/-- Étaleness is preserved along the actual normalization map. -/
instance normalizedPullback_toNormal_etale [Etale f] :
    Etale (pullback.fst (gluedPolynomialCover k m) f) := inferInstance

/-- The ORIGINAL field-valued point of an arbitrary source lifts to the actual
normalized pullback, with its equality to that same point proved. -/
theorem normalizedPullback_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Z) :
    ∃ s : Spec (.of K) ⟶ normalizedPullback k m f,
      s ≫ pullback.snd (gluedPolynomialCover k m) f = p := by
  obtain ⟨r, hr⟩ := gluedPolynomialCover_fieldPoint_lift k m K (p ≫ f)
  exact ⟨pullback.lift r p hr, pullback.lift_snd _ _ _⟩

/-- Any original point of ANY source over C_m lifts to the pullback of one
literal normalized P1 component, preserving the exact original point. -/
theorem componentPullback_fieldPoint_lift (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Z) :
    ∃ (i : Fin m) (s : Spec (.of K) ⟶
      pullback (componentLine k m i ≫ gluedPolynomialCover k m) f),
      s ≫ pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f = p := by
  obtain ⟨i, r, hr⟩ := componentLine_fieldPoint_lift k m K (p ≫ f)
  exact ⟨i, pullback.lift r p hr, pullback.lift_snd _ _ _⟩


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.OverField.Curve
section PointComponent
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable {F : Type u} [Field F] (X : FScheme F) [Smooth X.hom]


variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : _root_.AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
include hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- In any actual finite étale cover of a genus-zero curve, the actual component
containing an original-field point maps isomorphically to the original target. -/
theorem pointComponent_genusZero_isIso
    {Y : FScheme F} (f : X ⟶ Y)
    (hY : Properties Y) [IsFinite f.left] [Etale f.left]
    (o : Spec (.of F) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hzero : coherentGenus F Y = 0) :
    IsIso ((pointComponentMap hnormal hcomp X (o default)).left ≫ f.left) := by
  obtain ⟨s, hs⟩ := pointComponent_point_lift hnormal hcomp X o
  let : IsFinite (pointComponentMap hnormal hcomp X (o default) ≫ f).left :=
    inferInstanceAs (IsFinite ((pointComponentMap hnormal hcomp X (o default)).left ≫ f.left))
  let : Etale (pointComponentMap hnormal hcomp X (o default) ≫ f).left :=
    inferInstanceAs (Etale ((pointComponentMap hnormal hcomp X (o default)).left ≫ f.left))
  apply connectedPointedFiniteEtale_genusZero_isIso hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical (pointComponentMap hnormal hcomp X (o default) ≫ f) hY s ?_
      hzero
  change s ≫ ((pointComponentMap hnormal hcomp X (o default)).left ≫ X.hom) = 𝟙 _
  rw [← Category.assoc, hs, ho]


end PointComponent
section LineIsomorphism
open Divisors
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : _root_.AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
variable {F : Type u} [Field F] {X Y : FScheme F}

include hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical
open Scheme.OverField.Curve.ProjectiveLine Scheme.PinchedLine

/-- A connected actual finite étale cover of the literal reciprocal affine-chart
line with an original-field point is an isomorphism over that same line. -/
theorem connectedPointedFiniteEtale_line_isIso
    (f : X ⟶ lineOver F) [IsFinite f.left] [Etale f.left] [ConnectedSpace X.left]
    (o : Spec (.of F) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) : IsIso f.left :=
  connectedPointedFiniteEtale_genusZero_isIso hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical
    f (line_curveProperties F) o ho (line_coherentGenus_zero F)

/-- The same theorem for the actual standard Proj projective line. -/
theorem connectedPointedFiniteEtale_projectiveLine_isIso
    (f : X ⟶ projectiveLineOver F) [IsFinite f.left] [Etale f.left] [ConnectedSpace X.left]
    (o : Spec (.of F) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) : IsIso f.left :=
  connectedPointedFiniteEtale_genusZero_isIso hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical
    f (projectiveLine_curveProperties F) o ho
    (projectiveLine_coherentGenus_zero F)


end LineIsomorphism
end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

variable {Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m)

/-- The same component pullback, over the original ground field through its normalized line. -/
abbrev componentCoverSource (i : Fin m) : FScheme k :=
  Over.mk (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f ≫
    Scheme.PinchedLine.lineStructure k)

/-- The original finite étale component pullback map to the same normalized line. -/
def componentCoverProjection (i : Fin m) :
    componentCoverSource k m f i ⟶ Scheme.PinchedLine.lineOver k :=
  Over.homMk (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f) rfl

/-- The component projection is a base change of the given finite cover. -/
instance componentCoverProjection_finite (i : Fin m) [IsFinite f] :
    IsFinite (componentCoverProjection k m f i).left :=
  inferInstanceAs (IsFinite (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f))
/-- The component projection is a base change of the given étale cover. -/
instance componentCoverProjection_etale (i : Fin m) [Etale f] :
    Etale (componentCoverProjection k m f i).left :=
  inferInstanceAs (Etale (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f))
/-- The same component pullback is smooth of relative dimension one. -/
instance componentCoverSource_smoothOne (i : Fin m) [Etale f] :
    SmoothOfRelativeDimension 1 (componentCoverSource k m f i).hom :=
  smoothOfRelativeDimension_comp 0 1
    (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f)
      (Scheme.PinchedLine.lineStructure k)
/-- The dimension-one smoothness supplies ordinary smoothness. -/
instance componentCoverSource_smooth (i : Fin m) [Etale f] :
    Smooth (componentCoverSource k m f i).hom :=
  SmoothOfRelativeDimension.smooth 1 _

/-- The component pullback structure map is the SAME original-field structure
through the arbitrary cover. -/
@[reassoc] theorem componentCoverSource_structure (i : Fin m) :
    (componentCoverSource k m f i).hom =
      pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f ≫ f ≫ structureMap k m := by
  change pullback.fst _ _ ≫ Scheme.PinchedLine.lineStructure k = _
  rw [← componentParameter_over k m i, ← Category.assoc (componentLine k m i),
    ← Category.assoc, pullback.condition, Category.assoc]

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : _root_.AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
include hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- Any actual finite étale cover of a split polygon with an original-field
point has an ACTUAL normal component mapping isomorphically to a literal
P1 component. The component, point lift, and isomorphism are all derived. -/
theorem exists_split_pointed_component
    [IsFinite f] [Etale f] (o : Spec (.of k) ⟶ Z)
    (ho : o ≫ f ≫ structureMap k m = 𝟙 _) :
    ∃ (i : Fin m) (s : Spec (.of k) ⟶ (componentCoverSource k m f i).left),
      s ≫ pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f = o ∧
      IsIso ((pointComponentMap hnormal hcomp (componentCoverSource k m f i) (s default)).left ≫
        (componentCoverProjection k m f i).left) := by
  obtain ⟨i, s, hs⟩ := componentPullback_fieldPoint_lift k m f k o
  refine ⟨i, s, hs, ?_⟩
  have hso : s ≫ (componentCoverSource k m f i).hom = 𝟙 _ := by
    rw [componentCoverSource_structure, ← Category.assoc, hs, ho]
  exact pointComponent_genusZero_isIso hnormal hcomp (componentCoverSource k m f i)
    hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical
    (componentCoverProjection k m f i)
      (Scheme.OverField.Curve.ProjectiveLine.line_curveProperties k)
    s hso (Scheme.OverField.Curve.ProjectiveLine.line_coherentGenus_zero k)


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

/-- Every point of a literal normalized component above the actual global
node locus is one of its two explicit original-field endpoint points. -/
theorem componentLine_node_preimage (i : Fin m) (x : Scheme.PinchedLine.lineGluing k)
    (hx : gluedPolynomialCover k m (componentLine k m i x) ∈ globalNodeLocus k m) :
    x = Scheme.PinchedLine.gluedBranchPoint k 0 ∨ x = Scheme.PinchedLine.gluedBranchPoint k 1 := by
  have hb : componentLine k m i x ∈ componentBoundaryBranches k m i := ⟨⟨x, rfl⟩, hx⟩
  rw [componentBoundaryBranches_eq] at hb
  rcases hb with h | h
  · exact Or.inl ((componentLine k m i).isOpenEmbedding.injective
      (h.trans (gluedBranch_on_component k m i 0).symm))
  · exact Or.inr ((componentLine k m i).isOpenEmbedding.injective
      (h.trans (gluedBranch_on_component k m i 1).symm))


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k]

/-- The literal k-valued point of the reciprocal line at affine coordinate a. -/
def lineFieldPoint (a : k) : Spec (.of k) ⟶ lineGluing k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
    pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k)

@[simp] theorem lineFieldPoint_structure (a : k) :
    lineFieldPoint k a ≫ lineStructure k = 𝟙 _ := by
  rw [lineFieldPoint, Category.assoc, lineStructure, pushout.inl_desc]
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact Polynomial.eval_C

@[simp] theorem lineFieldPoint_apply (a : k) :
    lineFieldPoint k a default = gluedBranchPoint k a := by
  apply congrArg (pushout.inl (normalizationOverlapInclusion k) (gluingToInfinity k))
  apply PrimeSpectrum.ext
  ext p
  rfl

end AlgebraicGeometry.Scheme.PinchedLine

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

theorem rationalPoint_propagates_component_intersection
    {C D Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m) (c : C ⟶ Z) (d : D ⟶ Z)
    (i j : Fin m) (hij : i ≠ j)
    (g : C ⟶ Scheme.PinchedLine.lineGluing k) (h : D ⟶ Scheme.PinchedLine.lineGluing k)
    [IsIso g] [IsClosedImmersion d]
    (hc : c ≫ f = g ≫ componentLine k m i ≫ gluedPolynomialCover k m)
    (hd : d ≫ f = h ≫ componentLine k m j ≫ gluedPolynomialCover k m)
    (hmeet : (Set.range c ∩ Set.range d).Nonempty) :
    ∃ o : Spec (.of k) ⟶ D, o ≫ d ≫ f ≫ structureMap k m = 𝟙 _ := by
  obtain ⟨z, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hmeet
  have hca := congrArg (fun q : C ⟶ cycleScheme k m => q a) hc
  have hdb := congrArg (fun q : D ⟶ cycleScheme k m => q b) hd
  simp only [Scheme.Hom.comp_apply] at hca hdb
  have hcollision := hca.symm.trans ((congrArg f (ha.trans hb.symm)).trans hdb)
  have hnode := componentLine_collision_node k m i j hij (g a) (h b) hcollision
  obtain ⟨t, ht⟩ : ∃ t : k, g a = Scheme.PinchedLine.gluedBranchPoint k t := by
    rcases componentLine_node_preimage k m i (g a) hnode with ht | ht
    · exact ⟨0, ht⟩
    · exact ⟨1, ht⟩
  let p : Spec (.of k) ⟶ C := Scheme.PinchedLine.lineFieldPoint k t ≫ inv g
  have hpg : p ≫ g = Scheme.PinchedLine.lineFieldPoint k t := by simp [p]
  have hpa : p default = a := by
    apply g.homeomorph.injective
    change (p ≫ g) default = g a
    rw [hpg, Scheme.PinchedLine.lineFieldPoint_apply, ht]
  let q := p ≫ c
  have hq : q default ∈ Set.range d := by
    refine ⟨b, ?_⟩
    change d b = c (p default)
    rw [hpa, ha, hb]
  have hqfield : q ≫ (f ≫ structureMap k m) = 𝟙 _ := by
    change p ≫ c ≫ f ≫ structureMap k m = 𝟙 _
    rw [← Category.assoc c f, hc]
    simp only [Category.assoc, componentParameter_over, p, IsIso.inv_hom_id_assoc,
      Scheme.PinchedLine.lineFieldPoint_structure]
  obtain ⟨o, ho, hofield⟩ := closedImmersion_rationalPoint_lift d k
    (f ≫ structureMap k m) q hq hqfield
  exact ⟨o, hofield⟩


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

theorem rationalPoint_propagates_at_node
    {C D Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m) (c : C ⟶ Z)
    (i j : Fin m) (g : C ⟶ Scheme.PinchedLine.lineGluing k) [IsIso g]
    (d : D ⟶ (componentCoverSource k m f j).left) [IsClosedImmersion d]
    (hc : c ≫ f = g ≫ componentLine k m i ≫ gluedPolynomialCover k m)
    (a : C) (b : D)
    (hmeet : c a = pullback.snd (componentLine k m j ≫ gluedPolynomialCover k m) f (d b))
    (hnode : f (c a) ∈ globalNodeLocus k m) :
    ∃ o : Spec (.of k) ⟶ D,
      o default = b ∧ o ≫ d ≫ (componentCoverSource k m f j).hom = 𝟙 _ := by
  have hca := congrArg (fun q : C ⟶ cycleScheme k m => q a) hc
  simp only [Scheme.Hom.comp_apply] at hca
  have hga : gluedPolynomialCover k m (componentLine k m i (g a)) ∈ globalNodeLocus k m :=
    hca ▸ hnode
  obtain ⟨t, ht⟩ : ∃ t : k, g a = Scheme.PinchedLine.gluedBranchPoint k t := by
    rcases componentLine_node_preimage k m i (g a) hga with ht | ht
    · exact ⟨0, ht⟩
    · exact ⟨1, ht⟩
  let p : Spec (.of k) ⟶ C := Scheme.PinchedLine.lineFieldPoint k t ≫ inv g
  have hpg : p ≫ g = Scheme.PinchedLine.lineFieldPoint k t := by simp [p]
  have hpa : p default = a := by
    apply g.homeomorph.injective
    change (p ≫ g) default = g a
    rw [hpg, Scheme.PinchedLine.lineFieldPoint_apply, ht]
  have hpn : p ≫ c ≫ f ≫ structureMap k m = 𝟙 _ := by
    rw [← Category.assoc c f, hc]
    simp only [Category.assoc, componentParameter_over, p, IsIso.inv_hom_id_assoc,
      Scheme.PinchedLine.lineFieldPoint_structure]
  have hdb : gluedPolynomialCover k m (componentLine k m j
      (pullback.fst (componentLine k m j ≫ gluedPolynomialCover k m) f (d b))) = f (c a) := by
    have hcond := congrArg (fun q : (componentCoverSource k m f j).left ⟶ cycleScheme k m => q (d
      b))
      (pullback.condition (f := componentLine k m j ≫ gluedPolynomialCover k m) (g := f))
    simp only [Scheme.Hom.comp_apply] at hcond
    exact hcond.trans (congrArg f hmeet.symm)
  obtain ⟨u, hu⟩ : ∃ u : k,
      pullback.fst (componentLine k m j ≫ gluedPolynomialCover k m) f (d b) =
        Scheme.PinchedLine.gluedBranchPoint k u := by
    rcases componentLine_node_preimage k m j _ (hdb ▸ hnode) with hu | hu
    · exact ⟨0, hu⟩
    · exact ⟨1, hu⟩
  obtain ⟨r, hr, hrl, hrz⟩ := pullback_rationalPoint_at k
    (componentLine k m j ≫ gluedPolynomialCover k m) f (structureMap k m)
    (Scheme.PinchedLine.lineFieldPoint k u) (p ≫ c)
    (by simp only [Category.assoc, componentParameter_over,
      Scheme.PinchedLine.lineFieldPoint_structure]) (by simpa only [Category.assoc] using hpn)
    (d b) (by simpa only [Scheme.PinchedLine.lineFieldPoint_apply] using hu)
    (by simpa only [Scheme.Hom.comp_apply, hpa] using hmeet.symm)
  obtain ⟨o, ho⟩ := closedImmersion_fieldPoint_lift d k r ⟨b, hr.symm⟩
  refine ⟨o, ?_, ?_⟩
  · apply d.isClosedEmbedding.injective
    calc
      d (o default) = r default := congrArg (fun q : Spec (.of k) ⟶ (componentCoverSource k m f
        j).left => q default) ho
      _ = d b := hr
  · rw [← Category.assoc, ho, componentCoverSource_structure, ← Category.assoc,
      hrz]
    simpa only [Category.assoc] using hpn


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

/-- The complement of the actual conductor node locus lies in the infinity
chart: the part of the affine chart outside the conductor is the gluing overlap. -/
theorem nonNode_mem_infinity (z : cycleScheme k m) (hz : z ∉ globalNodeLocus k m) :
    z ∈ Set.range (pushout.inr (gluingToNode k m) (gluingToInfinity k m)) := by
  rcases Scheme.openPushout_covered (gluingToNode k m) (gluingToInfinity k m) z with
    ⟨p, rfl⟩ | ⟨p, hp⟩
  · have hp : conductor k m ∉ p.asIdeal := by
      intro hp
      apply hz
      rw [globalNodeLocus_eq_conductorImage]
      exact ⟨p, hp, rfl⟩
    have hr : p ∈ (gluingToNode k m).opensRange := by
      change p ∈ ((conductorOpenIso k m).hom ≫ nodeOverlapInclusion k m).opensRange
      rw [Scheme.Hom.opensRange_comp_of_isIso]
      rw [show (nodeOverlapInclusion k m).opensRange = PrimeSpectrum.basicOpen (conductor k m)
        from Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k m)) (conductor k m)]
      exact hp
    obtain ⟨w, rfl⟩ := hr
    refine ⟨gluingToInfinity k m w, ?_⟩
    exact congrArg (fun h : overlapScheme k m ⟶ cycleScheme k m => h w)
      (pushout.condition (f := gluingToNode k m) (g := gluingToInfinity k m)).symm
  · exact ⟨p, hp⟩

/-- The normalized source has exactly one actual point over every nonnode. -/
theorem gluedPolynomialCover_eq_of_nonNode (a b : normalizedScheme k m)
    (hab : gluedPolynomialCover k m a = gluedPolynomialCover k m b)
    (ha : gluedPolynomialCover k m a ∉ globalNodeLocus k m) : a = b := by
  obtain ⟨y, hy⟩ := nonNode_mem_infinity k m _ ha
  exact ((gluedPolynomialCover_infinity_fibre k m y a).mp hy.symm).trans
    ((gluedPolynomialCover_infinity_fibre k m y b).mp (hab.symm.trans hy.symm)).symm

variable {Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m)

/-- After ANY actual scheme base change, the finite normalization projection
is injective over the complement of the actual conductor nodes. -/
theorem normalizedPullback_snd_eq_of_nonNode (a b : normalizedPullback k m f)
    (hab : pullback.snd (gluedPolynomialCover k m) f a =
      pullback.snd (gluedPolynomialCover k m) f b)
    (ha : f (pullback.snd (gluedPolynomialCover k m) f a) ∉ globalNodeLocus k m) : a = b := by
  let j := pushout.inr (normalizationOverlapInclusion k m) (gluingToInfinity k m)
  have hj : j ≫ gluedPolynomialCover k m =
      pushout.inr (gluingToNode k m) (gluingToInfinity k m) := by
    exact Scheme.OpenNormalizationGluing.infinity_chart
      (gluingToNode k m) (gluingToInfinity k m) (normalizationOverlapInclusion k m)
      (polynomialCover k m) (conductorOpenIso_over k m).symm
  have : IsOpenImmersion (j ≫ gluedPolynomialCover k m) := by rw [hj]; infer_instance
  have hc (t : normalizedPullback k m f) :
      gluedPolynomialCover k m (pullback.fst (gluedPolynomialCover k m) f t) =
        f (pullback.snd (gluedPolynomialCover k m) f t) :=
    congrArg (fun h : normalizedPullback k m f ⟶ cycleScheme k m => h t)
      (pullback.condition (f := gluedPolynomialCover k m) (g := f))
  obtain ⟨y, hy⟩ := nonNode_mem_infinity k m _ ha
  apply pullback_snd_eq_of_open_chart j (gluedPolynomialCover k m) f a b _ _ hab
  · exact ⟨y, ((gluedPolynomialCover_infinity_fibre k m y _).mp
      ((hc a).trans hy.symm)).symm⟩
  · exact ⟨y, ((gluedPolynomialCover_infinity_fibre k m y _).mp
      ((hc b).trans ((congrArg f hab).symm.trans hy.symm))).symm⟩

/-- The genuine base-changed component inclusion into the normalized pullback. -/
def componentPullbackToNormalized (i : Fin m) :
    pullback (componentLine k m i ≫ gluedPolynomialCover k m) f ⟶ normalizedPullback k m f :=
  pullback.map _ _ _ _ (componentLine k m i) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The actual component pullback inclusion is open by base change. -/
instance componentPullbackToNormalized_open (i : Fin m) :
    IsOpenImmersion (componentPullbackToNormalized k m f i) := by
  unfold componentPullbackToNormalized
  infer_instance

@[reassoc, simp] theorem componentPullbackToNormalized_fst (i : Fin m) :
    componentPullbackToNormalized k m f i ≫ pullback.fst (gluedPolynomialCover k m) f =
      pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f ≫ componentLine k m i := by
  simp [componentPullbackToNormalized]

@[reassoc, simp] theorem componentPullbackToNormalized_snd (i : Fin m) :
    componentPullbackToNormalized k m f i ≫ pullback.snd (gluedPolynomialCover k m) f =
      pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f := by
  simp [componentPullbackToNormalized]

/-- Points of two component pullbacks over the same nonnode necessarily have
the same actual normalized component index. -/
theorem componentPullback_index_eq_of_nonNode (i j : Fin m)
    (a : ↑(pullback (componentLine k m i ≫ gluedPolynomialCover k m) f))
    (b : ↑(pullback (componentLine k m j ≫ gluedPolynomialCover k m) f))
    (hab : pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a =
      pullback.snd (componentLine k m j ≫ gluedPolynomialCover k m) f b)
    (ha : f (pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a) ∉
      globalNodeLocus k m) : i = j := by
  have he : componentPullbackToNormalized k m f i a = componentPullbackToNormalized k m f j b := by
    apply normalizedPullback_snd_eq_of_nonNode k m f
    · simpa only [← Scheme.Hom.comp_apply, componentPullbackToNormalized_snd] using hab
    · simpa only [← Scheme.Hom.comp_apply, componentPullbackToNormalized_snd] using ha
  apply componentLine_index_eq k m i j
    (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f a)
    (pullback.fst (componentLine k m j ≫ gluedPolynomialCover k m) f b)
  simpa only [← Scheme.Hom.comp_apply, componentPullbackToNormalized_fst] using
    congrArg (pullback.fst (gluedPolynomialCover k m) f) he

/-- The same-component comparison is equality of the ACTUAL pullback points. -/
theorem componentPullback_eq_of_nonNode (i : Fin m)
    (a b : ↑(pullback (componentLine k m i ≫ gluedPolynomialCover k m) f))
    (hab : pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a =
      pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f b)
    (ha : f (pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a) ∉
      globalNodeLocus k m) : a = b := by
  apply (componentPullbackToNormalized k m f i).isOpenEmbedding.injective
  apply normalizedPullback_snd_eq_of_nonNode k m f
  · simpa only [← Scheme.Hom.comp_apply, componentPullbackToNormalized_snd] using hab
  · simpa only [← Scheme.Hom.comp_apply, componentPullbackToNormalized_snd] using ha

/-- The two component indices and actual pullback points agree over every
nonnode. Heterogeneous equality packages the canonical transport along i=j. -/
theorem componentPullback_compare_of_nonNode (i j : Fin m)
    (a : ↑(pullback (componentLine k m i ≫ gluedPolynomialCover k m) f))
    (b : ↑(pullback (componentLine k m j ≫ gluedPolynomialCover k m) f))
    (hab : pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a =
      pullback.snd (componentLine k m j ≫ gluedPolynomialCover k m) f b)
    (ha : f (pullback.snd (componentLine k m i ≫ gluedPolynomialCover k m) f a) ∉
      globalNodeLocus k m) : i = j ∧ HEq a b := by
  have hij := componentPullback_index_eq_of_nonNode k m f i j a b hab ha
  subst j
  exact ⟨rfl, heq_of_eq (componentPullback_eq_of_nonNode k m f i a b hab ha)⟩


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

variable {Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m)
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})

/-- The actual irreducible-component inventory of all literal P1 pullbacks.
No component count, degree, or permutation is part of this definition. -/
abbrev coverComponentIndex := Σ i : Fin m, irreducibleComponents (componentCoverSource k m f i).left

/-- The finite component cover of the proper line is Noetherian. -/
instance componentCoverSource_noetherian (i : Fin m) [IsFinite f] :
    IsNoetherian (componentCoverSource k m f i).left := by
  let : IsLocallyNoetherian (componentCoverSource k m f i).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f ≫
        Scheme.PinchedLine.lineStructure k)
  let : CompactSpace (componentCoverSource k m f i).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst (componentLine k m i ≫ gluedPolynomialCover k m) f ≫
        Scheme.PinchedLine.lineStructure k)
  exact ⟨⟩

/-- The actual component inventory is finite by Noetherianity. -/
instance coverComponentIndex_finite [IsFinite f] : Finite (coverComponentIndex k m f) := by
  let (i : Fin m) : Finite (irreducibleComponents (componentCoverSource k m f i).left) :=
    (NoetherianSpace.finite_irreducibleComponents (α := (componentCoverSource k m f
      i).left)).to_subtype
  infer_instance

variable [Etale f]

/-- The open defined by this actual irreducible component of the smooth component pullback. -/
def coverComponentOpen (v : coverComponentIndex k m f) :
    (componentCoverSource k m f v.1).left.Opens :=
  ⟨v.2.val, hcomp _ (LocallyOfFiniteType.isLocallyNoetherian (componentCoverSource k m f v.1).hom)
    (hnormal k _ (componentCoverSource k m f v.1).hom inferInstance) _ v.2.property⟩

/-- The actual open integral component with its inherited original-field structural map. -/
abbrev coverComponent (v : coverComponentIndex k m f) : FScheme k :=
  Over.mk ((coverComponentOpen k m f hnormal hcomp v).ι ≫ (componentCoverSource k m f v.1).hom)

/-- The actual component inclusion as a morphism over the original field. -/
def coverComponentInclusion (v : coverComponentIndex k m f) :
    coverComponent k m f hnormal hcomp v ⟶ componentCoverSource k m f v.1 :=
  Over.homMk (coverComponentOpen k m f hnormal hcomp v).ι rfl

/-- The actual normalized component projection to its original target line. -/
def coverComponentProjection (v : coverComponentIndex k m f) :
    coverComponent k m f hnormal hcomp v ⟶ Scheme.PinchedLine.lineOver k :=
  coverComponentInclusion k m f hnormal hcomp v ≫ componentCoverProjection k m f v.1

/-- The actual component mapped back into the given finite étale source. -/
def coverComponentToSource (v : coverComponentIndex k m f) :
    (coverComponent k m f hnormal hcomp v).left ⟶ Z :=
  (coverComponentInclusion k m f hnormal hcomp v).left ≫
    pullback.snd (componentLine k m v.1 ≫ gluedPolynomialCover k m) f

/-- The clopen actual component inclusion is closed. -/
instance coverComponentInclusion_closed (v : coverComponentIndex k m f) :
    IsClosedImmersion (coverComponentInclusion k m f hnormal hcomp v).left := by
  change IsClosedImmersion (coverComponentOpen k m f hnormal hcomp v).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_of_mem_irreducibleComponents _ v.2.property

/-- The open component inclusion is étale. -/
instance coverComponentInclusion_etale (v : coverComponentIndex k m f) :
    Etale (coverComponentInclusion k m f hnormal hcomp v).left :=
  inferInstanceAs (Etale (coverComponentOpen k m f hnormal hcomp v).ι)

/-- The actual component projection is finite by composition. -/
instance coverComponentProjection_finite (v : coverComponentIndex k m f) [IsFinite f] :
    IsFinite (coverComponentProjection k m f hnormal hcomp v).left :=
  inferInstanceAs (IsFinite ((coverComponentInclusion k m f hnormal hcomp v).left ≫
    (componentCoverProjection k m f v.1).left))

/-- The actual component projection is étale by composition. -/
instance coverComponentProjection_etale (v : coverComponentIndex k m f) :
    Etale (coverComponentProjection k m f hnormal hcomp v).left :=
  inferInstanceAs (Etale ((coverComponentInclusion k m f hnormal hcomp v).left ≫
    (componentCoverProjection k m f v.1).left))

/-- The selected actual irreducible component is connected. -/
instance coverComponent_connected (v : coverComponentIndex k m f) :
    ConnectedSpace (coverComponent k m f hnormal hcomp v).left := by
  let : IrreducibleSpace v.2.val := Subtype.irreducibleSpace v.2.property.1
  exact inferInstanceAs (ConnectedSpace v.2.val)

/-- The actual normalization-component map to the original source is finite. -/
instance coverComponentToSource_finite (v : coverComponentIndex k m f) :
    IsFinite (coverComponentToSource k m f hnormal hcomp v) := by
  let : IsClosedImmersion (componentLine k m v.1) :=
    IsClosedImmersion.of_isPreimmersion _ (componentLine_range_closed k m v.1)
  unfold coverComponentToSource
  infer_instance

@[reassoc] theorem coverComponentToSource_over (v : coverComponentIndex k m f) :
    coverComponentToSource k m f hnormal hcomp v ≫ f =
      (coverComponentProjection k m f hnormal hcomp v).left ≫
        componentLine k m v.1 ≫ gluedPolynomialCover k m := by
  dsimp [coverComponentToSource, coverComponentProjection, componentCoverProjection]
  rw [Category.assoc, ← pullback.condition]
  simp only [Category.assoc]

@[reassoc] theorem coverComponent_structure (v : coverComponentIndex k m f) :
    (coverComponent k m f hnormal hcomp v).hom =
      coverComponentToSource k m f hnormal hcomp v ≫ f ≫ structureMap k m := by
  change (coverComponentOpen k m f hnormal hcomp v).ι ≫
    (componentCoverSource k m f v.1).hom = _
  rw [componentCoverSource_structure]
  rfl

/-- These are actual nonempty closed images in the given cover source. -/
theorem coverComponent_image_nonempty (v : coverComponentIndex k m f) :
    (Set.range (coverComponentToSource k m f hnormal hcomp v)).Nonempty := by
  obtain ⟨a, ha⟩ := v.2.property.1.nonempty
  exact ⟨_, ⟨⟨a, ha⟩, rfl⟩⟩

theorem coverComponent_image_closed (v : coverComponentIndex k m f) :
    IsClosed (Set.range (coverComponentToSource k m f hnormal hcomp v)) := by
  simpa using (coverComponentToSource k m f hnormal hcomp v).isClosedMap _ isClosed_univ

/-- Exhaustive coverage by actual normalization-component images is derived
from the target normalization and actual scheme pullback points. -/
theorem coverComponent_images_cover (z : Z) :
    ∃ v : coverComponentIndex k m f,
      z ∈ Set.range (coverComponentToSource k m f hnormal hcomp v) := by
  obtain ⟨i, _, ⟨x, rfl⟩, hx⟩ := targetComponents_cover k m (f z)
  obtain ⟨a, ha, haz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := componentLine k m i ≫ gluedPolynomialCover k m) (g := f) x z hx
  let v : coverComponentIndex k m f :=
    ⟨i, ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩⟩
  refine ⟨v, ⟨⟨a, mem_irreducibleComponent⟩, ?_⟩⟩
  exact haz

include hnormal hcomp in
/-- Actual components of a smooth pullback cannot share a point. -/
theorem coverComponentIndex_eq_of_point (i : Fin m)
    (C D : irreducibleComponents (componentCoverSource k m f i).left)
    (x : (componentCoverSource k m f i).left) (hC : x ∈ C.val) (hD : x ∈ D.val) : C = D := by
  apply Subtype.ext
  have hDcl : IsClopen D.val := ⟨isClosed_of_mem_irreducibleComponents _ D.property,
    hcomp _ (LocallyOfFiniteType.isLocallyNoetherian (componentCoverSource k m f i).hom)
      (hnormal k _ (componentCoverSource k m f i).hom inferInstance) _ D.property⟩
  have hCD := C.property.1.2.isPreconnected.subset_isClopen hDcl ⟨x, hC, hD⟩
  exact Set.Subset.antisymm hCD (C.property.2 D.property.1 hCD)


end AlgebraicGeometry.Scheme.Polygon

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

variable {Z : Scheme.{u}} (f : Z ⟶ cycleScheme k m)
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable [Etale f]

/-- Distinct actual components cannot meet over a nonnode, by pullback injectivity. -/
theorem coverComponent_eq_of_nonNode
    (v w : coverComponentIndex k m f)
    (a : (coverComponent k m f hnormal hcomp v).left)
    (b : (coverComponent k m f hnormal hcomp w).left)
    (hab : coverComponentToSource k m f hnormal hcomp v a =
      coverComponentToSource k m f hnormal hcomp w b)
    (ha : f (coverComponentToSource k m f hnormal hcomp v a) ∉ globalNodeLocus k m) : v = w := by
  rcases v with ⟨i, C⟩
  rcases w with ⟨j, D⟩
  have hij := componentPullback_index_eq_of_nonNode k m f i j a.val b.val hab ha
  subst j
  have hab' := componentPullback_eq_of_nonNode k m f i a.val b.val hab ha
  have hCD := coverComponentIndex_eq_of_point k m f hnormal hcomp i C D a.val a.property
    (hab' ▸ b.property)
  subst D
  rfl

variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : _root_.AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
variable [IsFinite f]

include hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- The original rational point internally supplies an actually split member
of the entire actual normalization-component inventory. -/
theorem exists_split_coverComponent (o : Spec (.of k) ⟶ Z)
    (ho : o ≫ f ≫ structureMap k m = 𝟙 _) :
    ∃ v : coverComponentIndex k m f,
      IsIso (coverComponentProjection k m f hnormal hcomp v).left := by
  obtain ⟨i, s, hs, hiso⟩ := exists_split_pointed_component k m f hnormal hcomp hreg hclosed hdim
    hprod hbase hgen hnorm hfree hcanonical o ho
  exact ⟨⟨i, ⟨irreducibleComponent (s default),
    irreducibleComponent_mem_irreducibleComponents (s default)⟩⟩, hiso⟩

include hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- Original-field rationality on an actual component forces its SAME map to
its literal P1 target to be an isomorphism. -/
theorem coverComponent_isIso_of_point (v : coverComponentIndex k m f)
    (o : Spec (.of k) ⟶ (coverComponent k m f hnormal hcomp v).left)
    (ho : o ≫ (coverComponent k m f hnormal hcomp v).hom = 𝟙 _) :
    IsIso (coverComponentProjection k m f hnormal hcomp v).left :=
  connectedPointedFiniteEtale_line_isIso hnormal hcomp hreg hclosed hdim hprod hbase hgen
    hnorm hfree hcanonical (coverComponentProjection k m f hnormal hcomp v) o ho

include hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- Every actual normalization component of ANY connected finite etale cover
of a split polygon with an original-field rational point is a split projective
line, and its ACTUAL projection to the corresponding target line is an
isomorphism. This proves propagation for all m, including the self-node of
m=1, by finite connected incidence; no component count, supplied split family,
branch lift, geometric connectedness, or cover-classification premise occurs. -/
theorem all_coverComponents_isIso [ConnectedSpace Z]
    (o : Spec (.of k) ⟶ Z) (ho : o ≫ f ≫ structureMap k m = 𝟙 _)
    (v : coverComponentIndex k m f) :
    IsIso (coverComponentProjection k m f hnormal hcomp v).left := by
  apply finiteClosedCoverInduction
    (fun w : coverComponentIndex k m f => Set.range (coverComponentToSource k m f hnormal hcomp w))
    (coverComponent_image_closed k m f hnormal hcomp)
    (coverComponent_image_nonempty k m f hnormal hcomp)
    (coverComponent_images_cover k m f hnormal hcomp)
    (fun w => IsIso (coverComponentProjection k m f hnormal hcomp w).left) ?_ ?_ v
  · exact exists_split_coverComponent k m f hnormal hcomp hreg hclosed hdim hprod hbase
      hgen hnorm hfree hcanonical o ho
  · intro w w' hmeet hsplit
    obtain ⟨z, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hmeet
    by_cases hnode : f z ∈ globalNodeLocus k m
    · let : IsIso (coverComponentProjection k m f hnormal hcomp w).left := hsplit
      obtain ⟨q, hqb, hq⟩ := rationalPoint_propagates_at_node k m f
        (coverComponentToSource k m f hnormal hcomp w) w.1 w'.1
        (coverComponentProjection k m f hnormal hcomp w).left
        (coverComponentInclusion k m f hnormal hcomp w').left
        (coverComponentToSource_over k m f hnormal hcomp w) a b (ha.trans hb.symm)
        (by simpa only [ha] using hnode)
      exact coverComponent_isIso_of_point k m f hnormal hcomp hreg hclosed hdim hprod hbase
        hgen hnorm hfree hcanonical w' q hq
    · have he := coverComponent_eq_of_nonNode k m f hnormal hcomp w w' a b
        (ha.trans hb.symm) (by simpa only [ha] using hnode)
      rwa [← he]


end AlgebraicGeometry.Scheme.Polygon
