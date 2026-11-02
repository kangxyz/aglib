/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree.Isomorphism
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.FieldPoint.Core
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula

/-! # Original coherent Euler characteristic of a smooth proper curve

The complete numerical Riemann--Roch construction uses the original coherent
cohomology and its structural scalar action. It is independent of Picard strata.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.OverField.Curve

section RiemannRoch

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
/-- The dimension of `H^q(X, M)` for the structural action of `X ⟶ Spec k` is the `finrank` of
`moduleCohomology`; the two actions agree by `moduleCohomologyModuleOfHom_constants`, used here so
that the kernel does not unfold both module structures again. -/
theorem moduleCohomologyDimension_eq_finrank_moduleCohomology (M : X.left.Modules) (q : ℕ) :
    moduleCohomologyDimension X.hom M q = Module.finrank k (moduleCohomology k X M q) :=
  congrArg (fun inst => @Module.finrank k (moduleCohomology k X M q) _ _ inst)
    (moduleCohomologyModuleOfHom_constants X M q)

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
include hX in
/-- **The cohomology of a line bundle on a curve vanishes above degree one** (Grothendieck
vanishing, `noetherianSheafCohomology_vanishing`, for the Noetherian one-dimensional `X`). -/
theorem moduleCohomologyDimension_eq_zero_of_two_le (L : LineBundle X.left) {q : ℕ}
    (hq : 2 ≤ q) : moduleCohomologyDimension X.hom L.val q = 0 := by
  have := curveProperties_isNoetherian hX
  have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X.left L.val) q) :=
    noetherianSheafCohomology_vanishing X.left _ 1 q
      (by rw [curveProperties_dimension smoothFieldDimension hX]; rfl) (by omega)
  rw [moduleCohomologyDimension_eq_finrank_moduleCohomology]
  exact Module.finrank_zero_of_subsingleton

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
/-- **Riemann–Roch in Euler-characteristic form**: `χ(X, L) = deg L + 1 - g` for a line bundle `L`
on a smooth proper geometrically connected curve (`curveLineBundle_riemannRoch` with
`Curve.lineBundleRiemannRoch`, and `H^q(X, L) = 0` for `q ≥ 2`). -/
theorem moduleEulerChar_eq_curveDegree_add_one_sub_genus (L : LineBundle X.left) :
    moduleEulerChar X.hom L.val =
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX (classOf X.left L) + 1 - coherentGenus k X := by
  have hRR := curveLineBundle_riemannRoch smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula lineBundleRiemannRoch X hX L
  change ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (moduleCohomologyDimension X.hom L.val q : ℤ) = _
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      one_mul, neg_one_mul, moduleCohomologyDimension_eq_finrank_moduleCohomology]
    linarith
  · intro q hq
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hq
    have h0 := moduleCohomologyDimension_eq_zero_of_two_le X hX L (q := q) (by omega)
    simp only [h0, Nat.cast_zero, mul_zero]

end RiemannRoch

end AlgebraicGeometry.Scheme.OverField.Curve
