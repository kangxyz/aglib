/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Trace

/-!
# The trace `H^2(X, μ_n) ≅ ℤ/n` of a smooth proper curve

The examples restate, for a smooth proper geometrically connected curve over an algebraically
closed field and `n` invertible in the field, that the degree is surjective with kernel
`n`-divisible modulo `n`, that `Pic(X)/n ≅ ℤ/n` and `Pic(X)/n ≅ H^2(X, μ_n)`, and that the trace
sends the Kummer boundary of a class to its degree and that of `𝒪(p)` to `1`, and guard the
axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField GroupCohomology.Kummer.Coefficients

universe w u

namespace AglibTest.CurveCohomologyTrace

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- The line bundle of a rational point has degree one, and the degree is surjective. -/
example (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX
        (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX p hp)) = 1 ∧
      Function.Surjective (Curve.curveDegree smoothFieldNormality normalComponentsOpen
        smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX) :=
  ⟨Curve.curveDegree_positiveLineBundle hX p hp, Curve.curveDegree_surjective_of_isAlgClosed hX⟩

/-- The degree modulo `n` is surjective with kernel `n Pic(X)`. -/
example : Function.Surjective (Curve.curveDegreeMod hX n) ∧
    (Curve.curveDegreeMod hX n).ker = (nsmulAddMonoidHom (α := PicardGroup X.left) n).range :=
  ⟨Curve.curveDegreeMod_surjective_of_isAlgClosed hX n,
    Curve.curveDegreeMod_ker_of_isUnit_of_isAlgClosed hX n hunit⟩

/-- `Pic(X)/n ≃+ ℤ/n`, sending a class to its degree modulo `n`. -/
example (c : PicardGroup X.left) :
    Curve.picardQuotientDegreeEquiv hX n hunit (QuotientAddGroup.mk c) =
      (Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX c : ZMod n) :=
  Curve.picardQuotientDegreeEquiv_mk hX n hunit c

/-- `Pic(X)/n ≃+ H^2(X, μ_n)` through the Kummer boundary. -/
example (c : PicardGroup X.left ⧸ (nsmulAddMonoidHom (α := PicardGroup X.left) n).range) :
    haveI := Curve.curveProperties_locallyOfFiniteType hX
    haveI := hX.proper
    haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    Curves.picardQuotientBoundaryAddEquiv.{u, w} k X.left X.hom hX.topologicalKrullDim_eq_one.le
        n hn hunit hinv c = Picard.picardQuotientBoundary X.left n hn hinv c := by
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact Curves.picardQuotientBoundaryAddEquiv_apply _ _ _ _ _ _ _ _ _

/-- The trace `H^2(X, μ_n) ≃+ ℤ/n` sends the boundary of a class to its degree modulo `n`. -/
example (c : PicardGroup X.left) :
    Curves.traceAddEquiv.{u, w} hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv c) =
      (Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX c : ZMod n) :=
  Curves.traceAddEquiv_picardBoundary hX n hn hunit hinv c

/-- Normalization: the boundary of `𝒪(p)` has trace `1`. -/
example (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Curves.traceAddEquiv.{u, w} hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv
      (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX p hp))) = 1 :=
  Curves.traceAddEquiv_picardBoundary_positiveLineBundle hX n hn hunit hinv p hp

/-- Normalization at a closed point. -/
example (z : X.left) (hz : IsClosed ({z} : Set X.left)) :
    haveI := Curve.curveProperties_locallyOfFiniteType hX
    Curves.traceAddEquiv.{u, w} hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv
      (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX
        (pointOfClosedPoint X.hom z hz) (pointOfClosedPoint_comp X.hom z hz)))) = 1 :=
  Curves.traceAddEquiv_picardBoundary_closedPoint hX n hn hunit hinv z hz

end AglibTest.CurveCohomologyTrace









/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.picardQuotientBoundaryAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.picardQuotientBoundaryAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.picardQuotientBoundaryAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.picardQuotientBoundaryAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary_positiveLineBundle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary_positiveLineBundle

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary_closedPoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_picardBoundary_closedPoint

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_comp_picardBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_comp_picardBoundary
