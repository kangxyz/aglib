/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.DivisorClass
public import Aglib.AlgebraicGeometry.RationalPoint.BaseChange
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal

/-! # Original rational-point divisor classes under base change

The cartesian square of rational sections is derived from the actual section
identities. The original ideal pullback isomorphism and duality then transport
the singleton divisor class, with coefficient one. No genus or properness
hypothesis is used. This is a Picard-class statement, not an order-transport or
boundary-point bijection theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k K : Type u} [Field k] [Field K]
  {X Y : Scheme.{u}}

/-- Compatible rational sections of an actual cartesian structure square form
an actual cartesian divisor square. -/
theorem rationalSection_isPullback (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback b s.structureMap r.structureMap q)
    (h : s.sectionMap ≫ b = q ≫ r.sectionMap) :
    IsPullback q s.sectionMap r.sectionMap b :=
  RationalPoint.isPullback_section r s q b H h

/-- The singleton class of an actual rational point is the dual of its original
ideal, with the rational trivialization chosen internally on the generic chart. -/
theorem singletonClass_eq_idealDual [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (r : RationalPoint k X)
    (hI : IsLocallyRankOne X (Hom.idealModule r.sectionMap))
    (hdim : topologicalKrullDim X ≤ 1) :
    DivisorClass.divisorToPicard X hdim (Finsupp.single ⟨r.point, r.point_isClosed⟩ 1) =
      classOf X (dualLineBundle X ⟨Hom.idealModule r.sectionMap, hI⟩) := by
  exact (idealDual_class_eq_point X r hI hdim).symm

/-- The original Picard pullback carries a rational singleton divisor to its
compatible base-changed rational singleton. The section square, relative
Cartier property, and ideal comparison are constructed, not supplied as class
identifications. -/
theorem pullbackClass_singleton [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    [IsIntegral Y] [IsNoetherian Y]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback b s.structureMap r.structureMap q)
    (h : s.sectionMap ≫ b = q ≫ r.sectionMap)
    (hI : IsLocallyRankOne X (Hom.idealModule r.sectionMap))
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1) :
    pullbackClass b (DivisorClass.divisorToPicard X hdimX
      (Finsupp.single ⟨r.point, r.point_isClosed⟩ 1)) =
      DivisorClass.divisorToPicard Y hdimY
        (Finsupp.single ⟨s.point, s.point_isClosed⟩ 1) := by
  have hD : Hom.IsRelativeEffectiveCartier r.sectionMap r.structureMap :=
    ⟨⟨r.section_isClosedImmersion, hI⟩, by rw [r.section_comp]; infer_instance⟩
  have H' := rationalSection_isPullback r s q b H h
  have hD' := hD.of_isPullback H H'
  have hx := (singletonClass_eq_idealDual r hI hdimX).trans
    (classOf_dual X hD.idealLineBundle)
  have hy := (singletonClass_eq_idealDual s hD'.isLocallyRankOne hdimY).trans
    (classOf_dual Y hD'.idealLineBundle)
  exact (congrArg (pullbackClass b) hx).trans
    ((pullbackClass_neg b _).trans
      ((congrArg Neg.neg (hD.pullbackClass_classOf_idealLineBundle H H')).trans hy.symm))

/-- Smooth separated relative curves supply the actual rank-one point ideal;
no properness or genus condition is needed for singleton-class transport. -/
theorem pullbackClass_singleton_of_smooth [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    [IsIntegral Y] [IsNoetherian Y]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (r : RationalPoint k X) (s : RationalPoint K Y)
    [SmoothOfRelativeDimension 1 r.structureMap] [IsSeparated r.structureMap]
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback b s.structureMap r.structureMap q)
    (h : s.sectionMap ≫ b = q ≫ r.sectionMap)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1) :
    pullbackClass b (DivisorClass.divisorToPicard X hdimX
      (Finsupp.single ⟨r.point, r.point_isClosed⟩ 1)) =
      DivisorClass.divisorToPicard Y hdimY
        (Finsupp.single ⟨s.point, s.point_isClosed⟩ 1) :=
  pullbackClass_singleton r s q b H h
    (Hom.sectionIdeal_isLocallyRankOne Hom.smoothRelativeDivisorIdeal
      r.structureMap r.sectionMap r.section_comp) hdimX hdimY

/-- The rational section in the literal field base change, with no independently
chosen target point. -/
def baseChangedRationalPoint (r : RationalPoint k X)
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    RationalPoint K (pullback r.structureMap q) := r.baseChange q

/-- Singleton transport along the literal field-base-change projection, using
its actual lifted rational section. -/
theorem pullbackClass_singleton_fieldExtension [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (r : RationalPoint k X) (q : Spec (.of K) ⟶ Spec (.of k))
    [IsIntegral (pullback r.structureMap q)] [IsNoetherian (pullback r.structureMap q)]
    [∀ y : ClosedPoint (pullback r.structureMap q),
      IsDiscreteValuationRing ((pullback r.structureMap q).presheaf.stalk y.val)]
    [SmoothOfRelativeDimension 1 r.structureMap] [IsSeparated r.structureMap]
    (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim (show Scheme from pullback r.structureMap q) ≤ 1) :
    pullbackClass (pullback.fst r.structureMap q)
        (DivisorClass.divisorToPicard X hdimX
          (Finsupp.single ⟨r.point, r.point_isClosed⟩ 1)) =
      DivisorClass.divisorToPicard (pullback r.structureMap q) hdimY
        (Finsupp.single ⟨(baseChangedRationalPoint r q).point,
          (baseChangedRationalPoint r q).point_isClosed⟩ 1) :=
  pullbackClass_singleton_of_smooth r (baseChangedRationalPoint r q) q
    (pullback.fst r.structureMap q) (IsPullback.of_hasPullback _ _)
    (pullback.lift_fst _ _ _) hdimX hdimY

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
