/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Basic
public import Aglib.AlgebraicGeometry.Curves.AffineFiniteProjection
public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField.OpenRecovery
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.Curves.Regular
public import Aglib.AlgebraicGeometry.Stalk.ClosedPointDimension
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension
public import Aglib.AlgebraicGeometry.Normalization.FiniteTypeField

/-! # Compactifying the whole smooth affine curve

A finite projection to the affine line is normalized over the original
projective line. Whole-open recovery retains every source point. Normality and
exact dimension one then give smoothness over the algebraically closed field.
This does not assert smooth compactification over an imperfect field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme


open OverField in
/-- Every nonempty geometrically connected smooth affine curve over an
algebraically closed field is an open subscheme of a smooth proper
geometrically connected curve. The open source is literally the original U. -/
theorem exists_whole_affine_curve_compactification
    (k : Type u) [Field k] [IsAlgClosed k]
    (U : Scheme.{u}) [IsAffine U] [Nonempty U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ (X : FScheme k), Curve.Properties X ∧
      ∃ j : U ⟶ X.left, IsOpenImmersion j ∧ j ≫ X.hom = p := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton p
  let : IsIntegral U := isIntegral_of_connected_of_smooth p
  let : ∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x) :=
    fun x => (smoothFieldNormality k U p inferInstance x).2
  obtain ⟨q, hq, hdq, hqp⟩ :=
    exists_finite_dominant_affineLine_projection_of_smooth k U p
  let : IsFinite q := hq
  let : IsDominant q := hdq
  let P := ProjectiveLine.projectiveP1 k
  let a := ProjectiveLine.chart k (0 : Fin 2)
  let : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine.structureMap k)
  let : QuasiCompact a := inferInstance
  let g := FiniteNormalOpen.genericMap a q
  let : IsFinite g.fromNormalization :=
    FiniteNormalOpen.fromNormalization_isFinite a q
      (fun W _ => affineChart_nagata_of_finiteType_field k
        (ProjectiveLine.structureMap k) W)
  let Y : FScheme k := Over.mk (g.fromNormalization ≫ ProjectiveLine.structureMap k)
  let i : U ⟶ Y.left := FiniteNormalOpen.inclusion a q
  let : IsOpenImmersion i := inferInstanceAs
    (IsOpenImmersion (FiniteNormalOpen.inclusion a q))
  let : IsIntegral Y.left := inferInstanceAs (IsIntegral g.normalization)
  let : IsProper Y.hom :=
    inferInstanceAs (IsProper (g.fromNormalization ≫ ProjectiveLine.structureMap k))
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsNoetherian Y.left := ⟨⟩
  let : ∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y) :=
    fun y => (FiniteNormalOpen.normalization_normalStalks a q y).2
  have hdP : topologicalKrullDim P ≤ 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (PinchedLine.ProjectiveComparison.lineIsoP1 k).hom.homeomorph.isHomeomorph]
    exact PinchedLine.line_dimension_le_one k
  have hdY : topologicalKrullDim Y.left = 1 := by
    apply le_antisymm
    · exact g.fromNormalization.topologicalKrullDim_le_of_isFinite.trans hdP
    · calc
        1 = topologicalKrullDim U :=
          (smoothFieldDimension k U p 1 inferInstance inferInstance).symm
        _ ≤ topologicalKrullDim Y.left :=
          i.isOpenEmbedding.isInducing.topologicalKrullDim_le
  let : ∀ y : ClosedPoint Y.left,
      IsDiscreteValuationRing (Y.left.presheaf.stalk y.val) := fun y => by
    have hy : ringKrullDim (Y.left.presheaf.stalk y.val) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight]
      exact_mod_cast Curve.Picard.Degree.ProductFormula.closedPoint_coheight_one
        Y.left hdY y.val y.property
    exact CodimensionOnePoint.localRing_isDiscreteValuationRing ⟨y.val, hy⟩
  let : Smooth Y.hom := Smooth.of_regularStalks_of_perfectField k Y.hom
    (Curve.regularStalks_of_closedDVR Y.left hdY.le)
  have hY : Curve.Properties Y := by
    refine ⟨Curve.smoothOfRelativeDimension_one_of_closedDVR k Y.left Y.hom,
      inferInstance, ?_⟩
    exact Geometrically.geometricallyConnected_of_connected_algebraicClosure k Y.hom
      (Geometrically.connectedSpace_fieldBaseChange k (AlgebraicClosure k) Y.hom)
  refine ⟨Y, hY, i, inferInstance, ?_⟩
  change FiniteNormalOpen.inclusion a q ≫
    g.fromNormalization ≫ ProjectiveLine.structureMap k = p
  rw [FiniteNormalOpen.inclusion_over_assoc, ProjectiveLine.chart_over]
  simpa only [Polynomial.algebraMap_eq] using hqp

end AlgebraicGeometry.Scheme
