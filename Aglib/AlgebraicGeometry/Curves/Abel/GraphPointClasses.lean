/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.PointClasses

/-! # The actual Abel graph class is the original point difference

This identifies the line bundle itself in the Picard group, rather than only
its numerical degree. The curve may have arbitrary genus. The same original
graph maps are used on both sides; no Picard representability is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

variable {S X : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  {k : Type u} [Field k] (t : Spec (.of k) ⟶ S)
  (s : Spec (.of k) ⟶ X) (hs : s ≫ p = t)

/-- On the actual geometric curve, the original graph-difference class equals
its original rational-point divisor difference. -/
theorem abelClass_eq_pointDifference
    (hY : Properties (Over.mk (pullback.snd p t)))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) p t) ≤ 1) :
    let Y : FScheme k := Over.mk (pullback.snd p t)
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t s hs =
      DivisorClass.divisorToPicard Y.left hdim
        (PointDivisor.pointDivisor Y (Hom.graph p t s hs) (Hom.graph_snd p t s hs) 1 -
          PointDivisor.pointDivisor Y
            (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho]))
            (Hom.graph_snd p t _ _) 1) := by
  let Y : FScheme k := Over.mk (pullback.snd p t)
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  have h₁ := PointDivisor.positiveLineBundle_class_eq_pointDivisor Y hY
    (Hom.graph p t s hs) (Hom.graph_snd p t s hs) hdim
  have h₂ := PointDivisor.positiveLineBundle_class_eq_pointDivisor Y hY
    (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho])) (Hom.graph_snd p t _ _) hdim
  change -classOf Y.left (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal p t s hs) =
    _ at h₁
  change -classOf Y.left (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal p o ho t) =
    _ at h₂
  change Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho t s hs =
    DivisorClass.divisorToPicard Y.left hdim _
  rw [map_sub, ← h₁, ← h₂, Hom.abelClass_eq, sub_neg_eq_add]
  rfl

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
