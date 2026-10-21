/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Projective-line cohomology and geometric connectedness

The positive-degree untwisted cohomology vanishing is proved over every commutative ring on
literal standard-graded Proj, using the native ULift comparison and zero-twist sheaf isomorphism.
The projective line and the existing reciprocal normalization gluing have genus zero and geometric
connectedness. Source102–217 is reused from Nodal.LineGeometry with its exact lineIsoP1Over and
stalk/dimension statements.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/ProjectiveLine/Geometry.lean`: source ranges [[102, 387]];
SHA-256 `2525f48e2f263a0dc7414f20b3b3e7f12140ef916eed13f91e7a0d0770d7b1b2`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial TopologicalSpace
open scoped Polynomial
open AlgebraicGeometry.Scheme Polynomial.PinchedPair
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme (coherentH1 structureAddSheaf)
open AlgebraicGeometry.Scheme.OverField.Curve
universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine
open AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k]

/-- The full untwisted vanishing family, from
`twistingCohomology_subsingleton_of_neg_le_degree` at degree zero and
`ProjectiveSpace.twistingZeroIso` in Aglib revision
197ca0728db3cdf1552a6bcefeeda901e3377862. Source modules:
`Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology` and
`Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit`.
The coordinate type is lifted to the ring universe and returned to literal
`Fin` coordinates through the graded polynomial renaming equivalence, its
induced `Proj` isomorphism, and the canonical structure-cohomology pullback.
The scheme is the literal standard-graded Proj over every commutative ring. -/
theorem projectiveSpaceStructureCohomologyVanishing :
  ∀ (R : Type u) [CommRing R] (n q : ℕ), 0 < q →
    let := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)
    Subsingleton (Sheaf.H (structureAddSheaf
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) q) := by
  intro R _ n q hq
  let ι := ULift.{u} (Fin (n + 1))
  let := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)
  let := MvPolynomial.gradedAlgebra (σ := ι) (R := R)
  let e : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≅
      AlgebraicGeometry.ProjectiveSpace R ι :=
    AlgebraicGeometry.ProjectiveSpace.finUliftIso R (n + 1)
  have hTwist := Scheme.Cohomology.twistingCohomology_subsingleton_of_neg_le_degree
    R ι n Equiv.ulift 0 q
    (neg_nonpos.mpr (Int.natCast_nonneg n)) (ne_of_gt hq)
  let e₀ := (SheafOfModules.toSheaf
    (AlgebraicGeometry.ProjectiveSpace R ι).ringCatSheaf).mapIso
    (AlgebraicGeometry.ProjectiveSpace.twistingZeroIso R ι)
  let eH : AddCommGrpCat.of (Sheaf.H.{u + 1}
      (Scheme.Cohomology.moduleAddSheaf (AlgebraicGeometry.ProjectiveSpace R ι)
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R ι 0)) q) ≅
      AddCommGrpCat.of (Sheaf.H.{u + 1}
        (structureAddSheaf (AlgebraicGeometry.ProjectiveSpace R ι)) q) :=
    (Sheaf.functorH.{u + 1} _ q).mapIso e₀
  let : Subsingleton (Sheaf.H (structureAddSheaf (AlgebraicGeometry.ProjectiveSpace R ι)) q) :=
    ⟨fun a b => (ConcreteCategory.bijective_of_isIso eH.inv).1 (hTwist.allEq _ _)⟩
  let : IsIso e.hom := e.isIso_hom
  exact (Scheme.Cohomology.structureCohomologyPullback_bijective e.hom q).2.subsingleton

/-- The independent cohomology statement is applied to the literal projective
line. The genus is the existing finrank of its actual H¹. -/
theorem projectiveLine_coherentGenus_zero
    :
    coherentGenus k (projectiveLineOver k) = 0 := by
  let : Subsingleton (coherentH1 k (projectiveLineOver k)) :=
    projectiveSpaceStructureCohomologyVanishing k 1 1 (by decide)
  exact Module.finrank_zero_of_subsingleton

/-- Genus zero for the literal reciprocal gluing follows through the proved
isomorphism over k, with no genus label or arbitrary-target premise. -/
theorem line_coherentGenus_zero
    :
    coherentGenus k (lineOver k) = 0 := by
  rw [coherentGenus_iso (lineIsoP1Over k)]
  exact projectiveLine_coherentGenus_zero k

end AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine

namespace AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine
open AlgebraicGeometry.Scheme.PinchedLine
variable (k : Type u) [Field k]

/-- The polynomial affine-line structural map is geometrically integral. -/
instance affineLine_geometricallyIntegral : GeometricallyIntegral (Spec.algebraMap k k[X]) := by
  let e := Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv k
    PUnit.{u+1}).toRingEquiv.toCommRingCatIso.op
  have hm : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial PUnit.{u+1} k)))) := by
    change GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : k →+* MvPolynomial PUnit.{u+1} k)))
    rw [← AffineSpace.SpecIso_inv_over (n := PUnit.{u+1}) (.of k)]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral) _ _).mpr
      inferInstance
  have he : e.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap k (MvPolynomial PUnit.{u+1} k))) = Spec.algebraMap k k[X] :=
    Spec.map_algHom_algebraMap (MvPolynomial.uniqueAlgEquiv k PUnit.{u+1}).toAlgHom
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral) _ _).mpr hm

/-- The canonical two full polynomial charts of literal projective space. -/
def projectiveLineCover : (ProjectiveLine.projectiveP1 k).OpenCover where
  I₀ := Fin 2
  X := fun _ => Spec (.of k[X])
  f := ProjectiveLine.chart k
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨ProjectiveLine.chart_covered k, fun _ => inferInstance⟩

theorem branchMap_over (a : k) : branchMap k a ≫ Spec.algebraMap k k[X] = 𝟙 _ := by
  rw [branchMap, Spec.algebraMap, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

/-- Both projective charts contain the same actual rational point with coordinate one. -/
theorem unitPoint_common (i : Fin 2) :
    branchMap k 1 ≫ ProjectiveLine.chart k i = branchMap k 1 ≫ ProjectiveLine.chart k 0 := by
  fin_cases i
  · rfl
  · symm
    convert ProjectiveLine.chart_transition k k (1 : kˣ) using 1 <;>
      simp [Units.val_one, inv_one, branchMap]

/-- The actual coordinate-one point in the first polynomial chart of projective one-space. -/
def unitPoint : Spec (.of k) ⟶ ProjectiveLine.projectiveP1 k :=
  branchMap k 1 ≫ ProjectiveLine.chart k 0

theorem unitPoint_over : unitPoint k ≫ ProjectiveLine.structureMap k = 𝟙 _ := by
  rw [unitPoint, Category.assoc, ProjectiveLine.chart_over]
  exact branchMap_over k 1

/-- Every field base change is covered by connected polynomial lines with one
common rational point. No algebraic closedness or abstract P1 premise is used. -/
instance projectiveLine_geometricallyConnected : GeometricallyConnected
  (ProjectiveLine.structureMap k) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ s => ?_⟩
  let C := Scheme.Pullback.openCoverOfLeft (projectiveLineCover k) (ProjectiveLine.structureMap k) s
  have hc (i : Fin 2) : ConnectedSpace (C.X i) := by
    change ConnectedSpace (pullback (ProjectiveLine.chart k i ≫ ProjectiveLine.structureMap k) s
      : Scheme)
    rw [ProjectiveLine.chart_over]
    change ConnectedSpace (pullback (Spec.algebraMap k k[X]) s : Scheme)
    let : IsIntegral (pullback (Spec.algebraMap k k[X]) s) :=
      GeometricallyIntegral.geometrically_isIntegral s _ _ (.of_hasPullback _ _)
    infer_instance
  let p : Spec (.of K) ⟶ pullback (ProjectiveLine.structureMap k) s :=
    pullback.lift (s ≫ unitPoint k) (𝟙 _) (by simp [unitPoint_over])
  let q (i : Fin 2) : Spec (.of K) ⟶ C.X i :=
    pullback.lift (s ≫ branchMap k 1) (𝟙 _) (by
      change (s ≫ branchMap k 1) ≫ (ProjectiveLine.chart k i ≫ ProjectiveLine.structureMap k) = 𝟙
        _ ≫ s
      rw [ProjectiveLine.chart_over]
      change (s ≫ branchMap k 1) ≫ Spec.algebraMap k k[X] = _
      rw [Category.assoc, branchMap_over]
      simp)
  have hq (i : Fin 2) : q i ≫ C.f i = p := by
    apply pullback.hom_ext
    · simp only [C, q, Scheme.Pullback.openCoverOfLeft_f, projectiveLineCover,
        Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, p]
      change s ≫ branchMap k 1 ≫ ProjectiveLine.chart k i = s ≫ unitPoint k
      rw [unitPoint_common]
      rfl
    · simp [C, q, Scheme.Pullback.openCoverOfLeft_f, p]
  let x : Spec (.of K) := Nonempty.some inferInstance
  have hinter : (⋂ i : Fin 2, Set.range (C.f i)).Nonempty := by
    refine ⟨p x, Set.mem_iInter.mpr fun i => ⟨q i x, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hq]
  have hcover : (⋃ i : Fin 2, Set.range (C.f i)) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact C.exists_eq z
  have hconn : _root_.IsPreconnected (Set.univ : Set (pullback (ProjectiveLine.structureMap k) s
    : Scheme)) := by
    rw [← hcover]
    apply isPreconnected_iUnion hinter
    intro i
    let := hc i
    simpa only [Set.image_univ] using isPreconnected_univ.image _ (C.f i).continuous.continuousOn
  exact { isPreconnected_univ := hconn, toNonempty := ⟨p x⟩ }

/-- Geometric connectedness of the same reciprocal normalization gluing. -/
instance line_geometricallyConnected : GeometricallyConnected (lineStructure k) := by
  rw [← Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) _ _).mpr
    inferInstance

theorem line_curveProperties : Properties (lineOver k) :=
  ⟨line_smoothOne k, Scheme.PinchedLine.ProjectiveComparison.lineStructure_proper k,
    line_geometricallyConnected k⟩

theorem projectiveLine_curveProperties : Properties (projectiveLineOver k) := by
  refine ⟨?_, ProjectiveLine.structureMap_proper k, projectiveLine_geometricallyConnected k⟩
  change SmoothOfRelativeDimension 1 (ProjectiveLine.structureMap k)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).hom,
      Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over]
  infer_instance


end AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine
