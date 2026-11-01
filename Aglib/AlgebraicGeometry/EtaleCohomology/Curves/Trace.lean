/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DegreeQuotient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CohomologyConsequences

/-!
# The trace `H^2(X, μ_n) ≅ ℤ/n` of a smooth proper curve

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`) and `n` a positive integer invertible in `k`. Then
(Stacks, Étale Cohomology, Lemma 69.1, Tag 03RQ, case `q = 2`; Milne, *Lectures on Étale
Cohomology* v2.21, Prop. 14.2, p. 90; SGA 4, Exp. XVIII, (1.1.3.2)):

* `Curve.picardQuotientDegreeEquiv`: the degree induces `Pic(X)/n Pic(X) ≃+ ℤ/n`. The degree is
  surjective because the line bundle `𝒪(p)` of a rational point has degree one
  (`Curve.curveDegree_positiveLineBundle`), and its kernel `Pic⁰(X)` is `n`-divisible
  (`Curve.exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed`);
* `Curves.picardQuotientBoundaryAddEquiv`: for any scheme `Y` of finite type and dimension at most
  one over a separably closed field, the Kummer boundary induces `Pic(Y)/n Pic(Y) ≃+ H^2(Y, μ_n)`
  (injective on any scheme by `Picard.picardQuotientBoundary_injective`, surjective by
  `Curves.power_bijective_of_curve`);
* `Curves.traceAddEquiv`: the trace `H^2(X, μ_n) ≃+ ℤ/n`, the inverse of the second isomorphism
  followed by the first. It sends the Kummer boundary of a class `c` to `deg c mod n`
  (`Curves.traceAddEquiv_picardBoundary`); in particular the boundary of `𝒪(p)` goes to `1`
  (`Curves.traceAddEquiv_picardBoundary_positiveLineBundle`), and likewise for the rational point
  of a closed point.

## Sign convention

The boundary is `Kummer.picardBoundary`: Mathlib's connecting map `Sheaf.H.δ` of the Kummer
sequence `0 → μ_n → 𝔾_m → 𝔾_m → 0` (inclusion, then `n`-th power) in degree one, precomposed
with `Picard.picardCohomologyEquiv : Pic(X) ≃+ H^1(X, 𝔾_m)`, whose torsor of a line bundle `L`
is the sheaf of frames `L ≅ 𝒪`, with `𝔾_m` acting by scalar postcomposition. The trace is
normalized by `Tr(∂[𝒪(p)]) = 1`. This is the form of SGA 4½, [Cycle], 2.1.5, p. 139
(`Tr cl_n(P) = 1`, with `cl_n(D) = ∂ cl(D)` by [Cycle], Def. 2.1.2, p. 138): there the torsor of
`L` is `Isom(𝒪, L)` ([Cycle], 1.1.6, p. 132), the torsor of frames of `L^∨`, and [Cycle], 1.1.5
and 2.1.3 record two further signs between coboundary maps. The conventions of `Sheaf.H.δ` and
of the Ext description of torsors are not compared with those of [Cycle] here; the
normalization above is the defining property of `traceAddEquiv`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

section Broad

variable (k : Type u) [Field k] [IsSepClosed k]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] [CompactSpace Y]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]

/-- **`Pic(Y)/n Pic(Y) ≃+ H^2(Y, μ_n)` through the Kummer boundary**, for a scheme `Y` of finite
type and dimension at most one over a separably closed field `k` and `n > 0` invertible in `k`:
the boundary is injective on `Pic(Y)/n` on any scheme (`Picard.picardQuotientBoundary_injective`),
and surjective since `n` is injective on `H^2(Y, 𝔾_m)` (`power_bijective_of_curve`). -/
def picardQuotientBoundaryAddEquiv (hdim : topologicalKrullDim Y ≤ 1) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(Y, ⊤))) :
    PicardGroup Y ⧸ (nsmulAddMonoidHom (α := PicardGroup Y) n).range ≃+
      Sheaf.H.{w} (mu Y n) 2 :=
  AddEquiv.ofBijective (Picard.picardQuotientBoundary Y n hn hinv)
    (Kummer.picardQuotientBoundary_bijective_of_power_injective Y n hn hinv
      (power_bijective_of_curve k Y p hdim n hn hunit 2 le_rfl).injective)

@[simp] theorem picardQuotientBoundaryAddEquiv_apply (hdim : topologicalKrullDim Y ≤ 1) (n : ℕ)
    (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(Y, ⊤)))
    (c : PicardGroup Y ⧸ (nsmulAddMonoidHom (α := PicardGroup Y) n).range) :
    picardQuotientBoundaryAddEquiv k Y p hdim n hn hunit hinv c =
      Picard.picardQuotientBoundary Y n hn hinv c := rfl

end Broad

section Trace

open Scheme.OverField

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- **The trace `H^2(X, μ_n) ≃+ ℤ/n`** of a smooth proper geometrically connected curve over an
algebraically closed field, for `n > 0` invertible in `k` (Stacks, Étale Cohomology, Lemma 69.1,
Tag 03RQ, `q = 2`; SGA 4, Exp. XVIII, (1.1.3.2)–(1.1.3.3)): the inverse of the Kummer
isomorphism `Pic(X)/n ≃+ H^2(X, μ_n)` followed by the degree modulo `n`. -/
def traceAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) : Sheaf.H.{w} (mu X.left n) 2 ≃+ ZMod n :=
  haveI := Curve.curveProperties_locallyOfFiniteType hX
  haveI := hX.proper
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  (picardQuotientBoundaryAddEquiv k X.left X.hom hX.topologicalKrullDim_eq_one.le n hn hunit
    hinv).symm.trans (Curve.picardQuotientDegreeEquiv hX n hunit)

/-- The whole trace-boundary composite is the original degree modulo `n`. -/
theorem traceAddEquiv_comp_picardBoundary (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    (traceAddEquiv hX n hn hunit hinv).toAddMonoidHom.comp
        (Kummer.picardBoundary X.left n hn hinv) = Curve.curveDegreeMod hX n := by
  apply AddMonoidHom.ext
  intro c
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have h : (picardQuotientBoundaryAddEquiv k X.left X.hom hX.topologicalKrullDim_eq_one.le n hn
      hunit hinv).symm (Kummer.picardBoundary X.left n hn hinv c) = QuotientAddGroup.mk c := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  change Curve.picardQuotientDegreeEquiv hX n hunit
    ((picardQuotientBoundaryAddEquiv k X.left X.hom hX.topologicalKrullDim_eq_one.le n hn hunit
      hinv).symm (Kummer.picardBoundary X.left n hn hinv c)) = _
  rw [h, Curve.picardQuotientDegreeEquiv_mk]
  rfl

/-- The trace of the Kummer boundary of a class is its degree modulo `n`. -/
theorem traceAddEquiv_picardBoundary (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (c : PicardGroup X.left) :
    traceAddEquiv hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv c) =
      (Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension
        Curve.Picard.Degree.properCurveProductFormula X hX c : ZMod n) :=
  DFunLike.congr_fun (traceAddEquiv_comp_picardBoundary hX n hn hunit hinv) c

/-- Normalization for Aglib's boundary: the Kummer boundary of the line
bundle `𝒪(p)` of a rational point `p` has trace `1`. -/
theorem traceAddEquiv_picardBoundary_positiveLineBundle (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    traceAddEquiv hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv
      (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX p hp))) = 1 := by
  rw [traceAddEquiv_picardBoundary, Curve.curveDegree_positiveLineBundle, Int.cast_one]

/-- **Normalization at a closed point**: the Kummer boundary of the line bundle `𝒪(z)` of a
closed point `z`, through its rational point `pointOfClosedPoint`, has trace `1`. -/
theorem traceAddEquiv_picardBoundary_closedPoint (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤))) (z : X.left)
    (hz : IsClosed ({z} : Set X.left)) :
    haveI := Curve.curveProperties_locallyOfFiniteType hX
    traceAddEquiv hX n hn hunit hinv (Kummer.picardBoundary X.left n hn hinv
      (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX
        (pointOfClosedPoint X.hom z hz) (pointOfClosedPoint_comp X.hom z hz)))) = 1 :=
  traceAddEquiv_picardBoundary_positiveLineBundle hX n hn hunit hinv _ _

end Trace

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
