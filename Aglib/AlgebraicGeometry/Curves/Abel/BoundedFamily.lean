/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.GraphPointClasses
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.Abel.Naturality
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Aglib.AlgebraicGeometry.Modules.Invertible.FiniteTensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.RelativeFlat
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Properties
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components

/-! # The actual ordered graph-sum line-bundle family

The parameter scheme is the existing finite native product in `Over S`.
On the actual product curve, tensor the original graph-difference bundles
of its coordinates. The empty parameter is the actual base and the empty
bundle is the existing trivial line bundle.

Original coordinate lifts, original Picard pullbacks and original graph
base-change maps give specialization to each actual ordered tuple. Fibre
degree zero holds over arbitrary fields, using the proved finite Cartier
degree theorem, not algebraically closed residue-field weights.

This constructs the actual coefficient bundle needed for semicontinuity.
It does not construct a torsion locus, trivialize its power, assert Picard
representability, prove finiteness, or use proper base change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The actual ordered parameter scheme, the native finite product of copies
of the original curve over its original base. -/
def parameter (n : ℕ) : Over S := finiteProductOver (fun _ : Fin n => Over.mk p)

/-- The original coordinate projection of the native parameter scheme. -/
def coordinate (n : ℕ) (i : Fin n) : (parameter p n).left ⟶ X :=
  (finiteProductOverπ (fun _ : Fin n => Over.mk p) i).left

@[reassoc (attr := simp)]
theorem coordinate_over (n : ℕ) (i : Fin n) :
    coordinate p n i ≫ p = (parameter p n).hom :=
  (finiteProductOverπ (fun _ : Fin n => Over.mk p) i).w

/-- The native product lift of a tuple of actual sections over a test scheme. -/
def parameterPoint {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (s : Fin n → (T ⟶ X)) (hs : ∀ i, s i ≫ p = t) : T ⟶ (parameter p n).left :=
  (finiteProductOverLift (T := Over.mk t) (fun _ : Fin n => Over.mk p)
    (fun i => Over.homMk (s i) (hs i))).left

@[reassoc (attr := simp)]
theorem parameterPoint_over {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (s : Fin n → (T ⟶ X)) (hs : ∀ i, s i ≫ p = t) :
    parameterPoint p t s hs ≫ (parameter p n).hom = t :=
  (finiteProductOverLift (T := Over.mk t) (fun _ : Fin n => Over.mk p)
    (fun i => Over.homMk (s i) (hs i))).w

@[reassoc (attr := simp)]
theorem parameterPoint_coordinate {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (s : Fin n → (T ⟶ X)) (hs : ∀ i, s i ≫ p = t) (i : Fin n) :
    parameterPoint p t s hs ≫ coordinate p n i = s i := by
  exact congrArg Over.Hom.left (finiteProductOverLift_π (T := Over.mk t)
    (fun _ : Fin n => Over.mk p) (fun i => Over.homMk (s i) (hs i)) i)

instance parameter_isProper [IsProper p] (n : ℕ) : IsProper (parameter p n).hom :=
  @isProper_finiteProductOver S n (fun _ : Fin n => Over.mk p)
    (fun _ => inferInstanceAs (IsProper p))

/-- Over a Noetherian base the proper tuple parameter scheme is Noetherian. -/
theorem parameter_isNoetherian [IsNoetherian S] [IsProper p] (n : ℕ) :
    IsNoetherian (parameter p n).left := by
  let : IsLocallyNoetherian (parameter p n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (parameter p n).hom
  let : CompactSpace (parameter p n).left :=
    QuasiCompact.compactSpace_of_compactSpace (parameter p n).hom
  exact ⟨⟩

variable [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The actual ordered graph-sum family on the actual product curve. -/
def lineBundle (n : ℕ) : LineBundle (pullback p (parameter p n).hom) :=
  finiteTensorLineBundle _ (fun i : Fin n =>
    Hom.abelLineBundle Hom.smoothRelativeDivisorIdeal p o ho (parameter p n).hom
      (coordinate p n i) (coordinate_over p n i))

/-- The original class of the family is the sum of its original Abel classes. -/
theorem lineBundle_class (n : ℕ) :
    classOf _ (lineBundle p o ho n) = ∑ i : Fin n,
      Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho (parameter p n).hom
        (coordinate p n i) (coordinate_over p n i) :=
  classOf_finiteTensor _ _

/-- The actual graph-sum coefficient is relatively flat over the parameter
scheme because the original family projection is smooth, hence flat. -/
theorem lineBundle_relativeFlat (n : ℕ) :
    Modules.relativeFlat (pullback.snd p (parameter p n).hom) (lineBundle p o ho n).val := by
  let : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  exact relativeFlat_of_flat (pullback.snd p (parameter p n).hom) (lineBundle p o ho n)

/-- Restricting the actual family along the native tuple point gives the sum
of the original Abel classes of precisely that tuple. -/
theorem lineBundle_class_at_tuple {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (s : Fin n → (T ⟶ X)) (hs : ∀ i, s i ≫ p = t) :
    pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
      (parameterPoint_over p t s hs)) (classOf _ (lineBundle p o ho n)) =
        ∑ i, Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t (s i) (hs i) := by
  classical
  rw [lineBundle_class]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := Abel.abelClass_baseChange Hom.smoothRelativeDivisorIdeal
    Hom.relativeCartierIdealBaseChange moduleTensorPullback p o ho (parameter p n).hom t
    (coordinate p n i) (coordinate_over p n i) (parameterPoint p t s hs)
    (parameterPoint_over p t s hs)
  simpa only [PullbackTensor.Local.pullbackHom_apply, parameterPoint_coordinate] using h

/-- On the actual field fibre, specialization is the original point-divisor
class difference for each coordinate, in arbitrary genus. -/
theorem lineBundle_class_at_field_tuple
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {n : ℕ}
    (s : Fin n → (Spec (.of k) ⟶ X)) (hs : ∀ i, s i ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t)))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) p t) ≤ 1) :
    let Y : FScheme k := Over.mk (pullback.snd p t)
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
      (parameterPoint_over p t s hs)) (classOf _ (lineBundle p o ho n)) =
        ∑ i, Picard.DivisorClass.divisorToPicard Y.left hdim
          (PointDivisor.pointDivisor Y (Hom.graph p t (s i) (hs i))
            (Hom.graph_snd p t (s i) (hs i)) 1 -
          PointDivisor.pointDivisor Y (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho]))
            (Hom.graph_snd p t _ _) 1) := by
  let Y : FScheme k := Over.mk (pullback.snd p t)
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  rw [lineBundle_class_at_tuple]
  apply Finset.sum_congr rfl
  intro i hi
  exact Abel.abelClass_eq_pointDifference p o ho t (s i) (hs i) hY hdim

/-- Every actual field specialization has original degree zero. The field
need not be algebraically closed; each graph is a rational degree-one point. -/
theorem lineBundle_degree_at_field_tuple
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {n : ℕ}
    (s : Fin n → (Spec (.of k) ⟶ X)) (hs : ∀ i, s i ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t))) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY
      (pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
        (parameterPoint_over p t s hs)) (classOf _ (lineBundle p o ho n))) = 0 := by
  rw [lineBundle_class_at_tuple, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact Abel.curveDegree_abelClass smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula FiniteCartierDegree.finiteCartierIdealDegree
    Hom.smoothRelativeDivisorIdeal p o ho t (s i) (hs i) hY

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
