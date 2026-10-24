/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily
public import Aglib.AlgebraicGeometry.Curves.Picard.BoundedParameters.Points
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism

/-! # Original degree-zero bundles occur in the actual bounded graph family

The canonical isomorphism from the identity-base fibre to the original curve
identifies the original point ideals with the actual graph ideals. Thus the
bounded rational-point tuple theorem describes fibres of the actual finite
graph tensor family, not an unrelated Picard representative. The final theorem
retains an isomorphism of the actual pulled-back module sheaves.

Every parameter point is its native coordinate lift. Consequently the original
specialization and degree-zero statements apply to arbitrary field-valued
parameter points, including nonclosed points and the empty product.

No torsion locus, Picard representability or finiteness statement is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S Y : Scheme.{u}} (p : Y ⟶ S)

/-- A point of the native finite product is exactly the lift of its original
coordinate tuple. This includes the empty product. -/
theorem parameterPoint_reconstruct {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (a : T ⟶ (parameter p n).left) (ha : a ≫ (parameter p n).hom = t) :
    parameterPoint p t (fun i => a ≫ coordinate p n i)
      (fun i => by simp [Category.assoc, ha]) = a := by
  have h : finiteProductOverLift (T := Over.mk t) (fun _ : Fin n => Over.mk p)
      (fun i => Over.homMk (a ≫ coordinate p n i)
        (by simp [Category.assoc, ha])) = Over.homMk a ha := by
    apply finiteProductOver_hom_ext
    intro i
    rw [finiteProductOverLift_π]
    apply Over.OverMorphism.ext
    rfl
  exact congrArg Over.Hom.left h

variable [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ Y) (ho : o ≫ p = 𝟙 S)

/-- The original class formula at an arbitrary point of the actual parameter
scheme, without requiring the point to have been supplied as a tuple lift. -/
theorem lineBundle_class_at_point {T : Scheme.{u}} (t : T ⟶ S) {n : ℕ}
    (a : T ⟶ (parameter p n).left) (ha : a ≫ (parameter p n).hom = t) :
    pullbackClass (Hom.familyMap p (parameter p n).hom t a ha)
      (classOf _ (lineBundle p o ho n)) = ∑ i : Fin n,
        Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t (a ≫ coordinate p n i)
          (by simp [Category.assoc, ha]) := by
  classical
  rw [lineBundle_class]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Abel.abelClass_baseChange Hom.smoothRelativeDivisorIdeal
    Hom.relativeCartierIdealBaseChange moduleTensorPullback p o ho (parameter p n).hom t
    (coordinate p n i) (coordinate_over p n i) a ha

/-- Every field-valued parameter point has original fibre degree zero, over
arbitrary residue fields, not only algebraically closed constants. -/
theorem lineBundle_degree_at_field_point
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {n : ℕ}
    (a : Spec (.of k) ⟶ (parameter p n).left)
    (ha : a ≫ (parameter p n).hom = t)
    (hY : Properties (Over.mk (pullback.snd p t))) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY
      (pullbackClass (Hom.familyMap p (parameter p n).hom t a ha)
        (classOf _ (lineBundle p o ho n))) = 0 := by
  rw [lineBundle_class_at_point, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact Abel.curveDegree_abelClass smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula FiniteCartierDegree.finiteCartierIdealDegree
    Hom.smoothRelativeDivisorIdeal p o ho t (a ≫ coordinate p n i)
      (by simp [Category.assoc, ha]) hY

section OriginalCurve

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)
  [SmoothOfRelativeDimension 1 X.hom]

section IdentityFibre

variable [IsSeparated X.hom]

/-- The original point ideal pulls back along the canonical identity-base
fibre isomorphism to the actual graph ideal, by the canonical ideal map. -/
theorem pointIdeal_class_pullback_identity
    (s : Spec (.of k) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _) :
    pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))
      (classOf X.left (PointDivisor.idealLineBundle X hX s hs)) =
      classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal
        X.hom (𝟙 _) s hs) := by
  let b := pullback.fst X.hom (𝟙 (Spec (.of k)))
  let g := Hom.graph X.hom (𝟙 (Spec (.of k))) s hs
  have h : (𝟙 _) ≫ s = g ≫ b := by simp [g, b]
  let : IsIso (Hom.idealPullbackMap s g b (𝟙 _) h) :=
    Hom.idealPullbackMap_isIso_of_iso_square s g b (𝟙 _) h
  apply (class_eq_iff _ _ _).mpr
  exact ⟨asIso (Hom.idealPullbackMap s g b (𝟙 _) h)⟩

/-- The original positive point difference is exactly the identity-base Abel
class after canonical pullback; no genus-one point normalization is used. -/
theorem pointDifference_class_pullback_identity
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (s : Spec (.of k) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _) :
    pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))
      (classOf X.left (PointDivisor.positiveLineBundle X hX s hs) -
        classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) =
      Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho (𝟙 _) s hs := by
  change (PullbackTensor.Local.pullbackHom _)
    (-classOf X.left (PointDivisor.idealLineBundle X hX s hs) -
      -classOf X.left (PointDivisor.idealLineBundle X hX o ho)) = _
  rw [map_sub, map_neg, map_neg]
  simp only [PullbackTensor.Local.pullbackHom_apply,
    pointIdeal_class_pullback_identity, sub_neg_eq_add, Hom.abelClass_eq,
    Hom.originIdealLineBundle, Category.id_comp]

end IdentityFibre

variable [IsAlgClosed k] [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

include hX

/-- Every original degree-zero Picard class occurs in the actual genus-sized
graph family, with the canonical identity-base fibre map explicitly retained. -/
theorem exists_parameter_of_picardDegree_eq_zero
    (hdim : topologicalKrullDim X.left = 1)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (L : PicardGroup X.left)
    (hL : Picard.Degree.picardDegree X.left X.hom hdim.le
      (Picard.Degree.properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ a : Spec (.of k) ⟶ (parameter X.hom (coherentGenus k X)).left,
      ∃ ha : a ≫ (parameter X.hom (coherentGenus k X)).hom = 𝟙 _,
        pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k)))) L =
          pullbackClass (Hom.familyMap X.hom (parameter X.hom (coherentGenus k X)).hom
            (𝟙 _) a ha) (classOf _ (lineBundle X.hom o ho (coherentGenus k X))) := by
  obtain ⟨s, hs⟩ := Picard.exists_positivePoint_genus_tuple_of_picardDegree_eq_zero
    X hX hdim o ho L hL
  refine ⟨parameterPoint X.hom (𝟙 _) (fun i => (s i).val) (fun i => (s i).property),
    parameterPoint_over X.hom (𝟙 _) _ _, ?_⟩
  rw [lineBundle_class_at_tuple, hs]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin (coherentGenus k X), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact pointDifference_class_pullback_identity X hX o ho (s i).val (s i).property

/-- The bounded family parameterizes actual line bundles: the original bundle
and the actual family fibre are isomorphic after the canonical fibre pullbacks. -/
theorem exists_parameter_lineBundle_iso
    (hdim : topologicalKrullDim X.left = 1)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (L : LineBundle X.left)
    (hL : Picard.Degree.picardDegree X.left X.hom hdim.le
      (Picard.Degree.properCurveProductFormula k X.left X.hom hdim) (classOf X.left L) = 0) :
    ∃ a : Spec (.of k) ⟶ (parameter X.hom (coherentGenus k X)).left,
      ∃ ha : a ≫ (parameter X.hom (coherentGenus k X)).hom = 𝟙 _,
        Nonempty ((pullbackLineBundle (pullback.fst X.hom (𝟙 (Spec (.of k)))) L).val ≅
          (pullbackLineBundle (Hom.familyMap X.hom
            (parameter X.hom (coherentGenus k X)).hom (𝟙 _) a ha)
            (lineBundle X.hom o ho (coherentGenus k X))).val) := by
  obtain ⟨a, ha, h⟩ := exists_parameter_of_picardDegree_eq_zero X hX hdim o ho
    (classOf X.left L) hL
  exact ⟨a, ha, (class_eq_iff _ _ _).mp h⟩

end OriginalCurve

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
