/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveOrder

/-!
# Order transport through the original curve stalk isomorphism

The normalized discrete valuation is invariant under ring equivalence.
Specialization uses the equivalence induced by the original scheme stalk
map, retaining the actual points and the original numerator/denominator.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace IsDiscreteValuationRing

/-- The intrinsic normalized additive valuation is unchanged by a ring
isomorphism. No compatible valuation is supplied as a premise. -/
theorem addVal_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    (e : R ≃+* S) (a : R) : addVal S (e a) = addVal R a := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, addVal_zero]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, v, hv⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [addVal_def a v hπ n hv]
  apply addVal_def (e a) (Units.map e.toMonoidHom v) (hπ.map e) n
  change e a = e (v : R) * e π ^ n
  simpa only [map_mul, map_pow] using congrArg e hv

end IsDiscreteValuationRing

namespace AlgebraicGeometry.Scheme.CodimensionOnePoint

universe u

/-- Finite order is preserved by the actual original stalk map at a surviving
curve generic point. The image codimension-one point has its literal scheme
image as its value, not an unrelated chosen DVR. -/
theorem finiteOrder_stalkMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z)]
    [∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)]
    (x : CodimensionOnePoint X) (f : X ⟶ Y)
    (hy : ringKrullDim (Y.presheaf.stalk (f x.val)) = 1)
    [IsIso (f.stalkMap x.val)] (a : Y.presheaf.stalk (f x.val)) :
    x.finiteOrder (f.stalkMap x.val a) =
      finiteOrder (X := Y) ⟨f x.val, hy⟩ a := by
  let y : CodimensionOnePoint Y := ⟨f x.val, hy⟩
  let : IsDiscreteValuationRing y.localRing := localRing_isDiscreteValuationRing y
  let : IsDiscreteValuationRing x.localRing := localRing_isDiscreteValuationRing x
  let e : y.localRing ≃+* x.localRing := RingEquiv.ofBijective
    (f.stalkMap x.val).hom (ConcreteCategory.bijective_of_isIso (f.stalkMap x.val))
  exact congrArg ENat.toNat (IsDiscreteValuationRing.addVal_ringEquiv e a)

end AlgebraicGeometry.Scheme.CodimensionOnePoint
