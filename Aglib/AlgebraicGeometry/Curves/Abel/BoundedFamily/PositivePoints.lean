/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Positive
public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Parameters

/-!
# Original positive graph families on arbitrary field fibres

Specialize the already proved whole positive-family pullback formula to a
field test. Each original graph ideal is the ideal of its actual rational
point on the native base-changed curve. The resulting positive divisor
class has no origin subtraction. The field and its structural base map
are arbitrary; no algebraic closure or new Picard representative is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S X : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive family on an arbitrary field test is the class
of the actual sum of its rational graph points on the native curve fibre. -/
theorem positiveFamilyLineBundle_class_at_field_tuple
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) {n : ℕ}
    (s : Fin n → (Spec (.of K) ⟶ X)) (hs : ∀ i, s i ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t)))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) p t) ≤ 1) :
    let Y : FScheme K := Over.mk (pullback.snd p t)
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
      (parameterPoint_over p t s hs)) (classOf _ (positiveFamilyLineBundle p n)) =
      ∑ i, Picard.DivisorClass.divisorToPicard Y.left hdim
        (PointDivisor.pointDivisor Y (Hom.graph p t (s i) (hs i))
          (Hom.graph_snd p t (s i) (hs i)) 1) := by
  let Y : FScheme K := Over.mk (pullback.snd p t)
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  rw [positiveFamilyLineBundle_class_at_tuple]
  apply Finset.sum_congr rfl
  intro i _
  have h := PointDivisor.positiveLineBundle_class_eq_pointDivisor Y hY
    (Hom.graph p t (s i) (hs i)) (Hom.graph_snd p t (s i) (hs i)) hdim
  change -classOf Y.left (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal p t
    (s i) (hs i)) = _ at h
  exact h

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
