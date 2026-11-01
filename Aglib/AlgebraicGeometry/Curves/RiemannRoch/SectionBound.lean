/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact

/-!
# Bounding sections by an effective divisor modification

If A <= B and H0(O(A)) vanishes, the original map from H0(O(B)) to the
finite-support quotient is injective. Its dimension is therefore bounded by
the actual residue-weighted degree of B-A. No genus bound or properness is
needed for this implication. The nonspecial degree-g construction uses a
single rational-point modification, whose quotient degree is one.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Cohomology
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

variable {k : Type u} [Field k] (X : FScheme k)
  [IsIntegral X.left] [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

-- The actual divisor short complex and its cohomology use native definitionally equal modules.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing of the original H0 kernel bounds sections by the actual
finite-support quotient degree, retaining all residue-field weights. -/
theorem divisorH0_finrank_le_quotientDegree (hdim : topologicalKrullDim X.left ≤ 1)
    {A B : Divisor X.left} (hAB : A ≤ B)
    [Subsingleton (moduleCohomology k X (divisorSheaf X.left A) 0)] :
    (Module.finrank k (moduleCohomology k X (divisorSheaf X.left B) 0) : ℤ) ≤
      Degree.degDiv X.left X.hom (B - A) := by
  let S := divisorQuotientSequence X.left hAB
  have hS : S.ShortExact := divisorQuotientSequence_shortExact X.left hAB
  have : Subsingleton (moduleCohomology k X S.X₁ 0) :=
    inferInstanceAs (Subsingleton (moduleCohomology k X (divisorSheaf X.left A) 0))
  have he := moduleCohomologyMap_exact X S hS 0
  have hinj : Function.Injective (moduleCohomologyMap X S.g 0) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact he).mpr
    ext x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have : Module.Finite k (moduleCohomology k X S.X₃ 0) :=
    divisorQuotientH0_finite X hdim hAB
  have hb := LinearMap.finrank_le_finrank_of_injective hinj
  have hb' : (Module.finrank k (moduleCohomology k X S.X₂ 0) : ℤ) ≤
      (Module.finrank k (moduleCohomology k X S.X₃ 0) : ℤ) := by exact_mod_cast hb
  exact hb'.trans_eq (divisorQuotientH0_finrank X hdim hAB)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
