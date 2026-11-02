/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Sections
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Separation.Basic

/-!
# Point degree and surjectivity of curve degree

A rational-point line bundle has degree one over any field. A smooth proper geometrically
connected curve over an algebraically closed field has a closed rational point, so its degree
and degree modulo every natural integer are surjective. This is the degree-one calculation
in Stacks, Tag 03RQ, and Milne, Lectures on Étale Cohomology v2.21, Proposition 14.2, p. 90.
No Jacobian divisibility result is imported.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

section Degree

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

/-- **The line bundle `𝒪(p)` of a rational point has degree one**: `𝒪(p)` is the dual of the
ideal sheaf of `p` (`PointDivisor.positiveLineBundle`). -/
theorem curveDegree_positiveLineBundle (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX (classOf X.left (PointDivisor.positiveLineBundle X hX p hp)) = 1 :=
  Abel.curveDegree_positive_section smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula Abel.FiniteCartierDegree.finiteCartierIdealDegree
    X hX p hp (PointDivisor.idealLineBundle X hX p hp).property

include hX in
/-- **The degree of a curve over an algebraically closed field is surjective**: the multiples of
the line bundle of a rational point realize every degree. -/
theorem curveDegree_surjective_of_isAlgClosed [IsAlgClosed k] :
    Function.Surjective (curveDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Picard.Degree.properCurveProductFormula X hX) := by
  have := curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : Nonempty X.left := curveProperties_nonempty hX
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty : (Set.univ : Set X.left).Nonempty)
  let o := pointOfClosedPoint X.hom z hz
  have ho : o ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom z hz
  intro d
  refine ⟨d • classOf X.left (PointDivisor.positiveLineBundle X hX o ho), ?_⟩
  rw [map_zsmul, curveDegree_positiveLineBundle, smul_eq_mul, mul_one]

/-- The degree modulo `n`, as a homomorphism `Pic(X) →+ ℤ/n`. -/
def curveDegreeMod (n : ℕ) : PicardGroup X.left →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (curveDegree smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula X hX)

@[simp] theorem curveDegreeMod_apply (n : ℕ) (c : PicardGroup X.left) :
    curveDegreeMod hX n c = (curveDegree smoothFieldNormality normalComponentsOpen
      smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
      Picard.Degree.properCurveProductFormula X hX c : ZMod n) := rfl

/-- The degree modulo `n` is surjective over an algebraically closed field. -/
theorem curveDegreeMod_surjective_of_isAlgClosed [IsAlgClosed k] (n : ℕ) :
    Function.Surjective (curveDegreeMod hX n) :=
  (ZMod.intCast_surjective).comp (curveDegree_surjective_of_isAlgClosed hX)

end Degree

end AlgebraicGeometry.Scheme.OverField.Curve
