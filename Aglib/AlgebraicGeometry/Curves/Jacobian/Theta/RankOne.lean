/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.NonSpecial
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.SectionBound

/-!
# A nonspecial line bundle of degree equal to the genus

Start with the actual degree-(g-1) line bundle with no sections and add one
rational-point divisor. The original divisor quotient has degree one, so
the actual H0 map bounds the new section dimension by one. Riemann--Roch
then makes that dimension exactly one and H1 dimension zero. This supplies
a nonempty point for the rank-one Abel open; openness and the universal
family on that open remain subsequent constructions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.Cohomology Scheme.RelativePicard
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Picard.DivisorClass Picard.DivisorInverse Picard.Degree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

include P R

-- Use the original divisor/module/cohomology realizations at every comparison.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In positive genus there is an actual degree-g line bundle with h0=1
and h1=0. No chosen base point occurs in the conclusion. -/
theorem exists_lineBundle_degree_genus_h0_one_h1_zero (hg : 0 < coherentGenus k X) :
    ∃ L : LineBundle X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
        X hX (classOf X.left L) = (coherentGenus k X : ℤ) ∧
      Module.finrank k (moduleCohomology k X L.val 0) = 1 ∧
      Module.finrank k (moduleCohomology k X L.val 1) = 0 := by
  let := hX.smooth
  let := hX.proper
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := hX.topologicalKrullDim_eq_one
  obtain ⟨L, hLdegree, hLsections⟩ :=
    exists_lineBundle_noSections_of_degree_lt_genus hX P R (coherentGenus k X - 1) (by omega)
  obtain ⟨D, ⟨e⟩⟩ := exists_divisor_iso X.left L.val L.property hd.le
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  let E : Divisor X.left := Finsupp.single (PointDivisor.closedPoint X o ho) 1
  let B : Divisor X.left := D + E
  have hDL : lineBundleDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) L =
        ((coherentGenus k X - 1 : ℕ) : ℤ) := hLdegree
  have hDdegree : degDiv X.left X.hom D = ((coherentGenus k X - 1 : ℕ) : ℤ) := by
    rw [← lineBundleDegree_divisor X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)]
    exact (lineBundleDegree_iso X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)
      (L := L) (N := divisorLineBundle X.left hd.le D) e).symm.trans hDL
  have hEdegree : degDiv X.left X.hom E = 1 := by
    simp only [E, degDiv_single, weight_eq_one, mul_one]
  have hBdegree : degDiv X.left X.hom B = (coherentGenus k X : ℤ) := by
    change degDiv X.left X.hom (D + E) = _
    rw [map_add, hDdegree, hEdegree]
    omega
  have hDB : D ≤ B := by
    intro x
    change D x ≤ D x + E x
    have heff : 0 ≤ E x := by
      by_cases hx : x = PointDivisor.closedPoint X o ho
      · simp only [E, hx, Finsupp.single_eq_same]
        norm_num
      · simp only [E, Finsupp.single_eq_of_ne hx, le_refl]
    omega
  have : Subsingleton (moduleCohomology k X L.val 0) := by
    refine ⟨fun a b => (moduleH0Equiv X L.val).injective ?_⟩
    exact (hLsections _).trans (hLsections _).symm
  have : Subsingleton (moduleCohomology k X (divisorSheaf X.left D) 0) :=
    (moduleCohomologyIso X e 0).symm.injective.subsingleton
  have hbound := divisorH0_finrank_le_quotientDegree X hd.le hDB
  have hquotient : degDiv X.left X.hom (B - D) = 1 := by
    simpa only [B, add_sub_cancel_left] using hEdegree
  rw [hquotient] at hbound
  let M := divisorLineBundle X.left hd.le B
  have hMdegree : lineBundleDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) M = (coherentGenus k X : ℤ) :=
    (lineBundleDegree_divisor X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) B).trans hBdegree
  have hrr := lineBundleRiemannRoch k X hd.le
    (properCurveProductFormula k X.left X.hom hd) M inferInstance
    (constants_bijective_of_proper_of_isAlgClosed X)
  rw [hMdegree] at hrr
  have hbound' : (Module.finrank k (moduleCohomology k X M.val 0) : ℤ) ≤ 1 := hbound
  refine ⟨M, hMdegree, ?_, ?_⟩ <;> omega

end AlgebraicGeometry.Scheme.OverField.Curve
