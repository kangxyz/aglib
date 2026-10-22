/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.GenericFormalFiber
public import Aglib.RingTheory.RegularLocalRing.Reduced

/-! # Regular finite generic formal fibres supply the completion condition -/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AdicCompletion

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The finite-extension regularity test supplied by the standard generic
geometrically regular formal fibre implies the intrinsic coefficient condition.
This is not, by itself, a theorem with a named excellence hypothesis. -/
theorem hasGeometricallyReducedFractionCompletion_of_regularFiniteGenericFormalFibres
    (h : ∀ (E : Type u) [Field E] [Algebra R E] [Algebra (FractionRing R) E]
      [IsScalarTower R (FractionRing R) E] [FiniteDimensional (FractionRing R) E],
      IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] E)) :
    HasGeometricallyReducedFractionCompletion R := by
  apply hasGeometricallyReducedFractionCompletion_of_finiteGenericFormalFibres R
  intro E _ _ _ _ _
  let := h E
  exact IsRegularRing.isReduced_of_regular
    (AdicCompletion (maximalIdeal R) R ⊗[R] E)

end AdicCompletion
