/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Reflexive
public import Aglib.RingTheory.Reflexive.Pi

/-! Reflexivity of actual normalizations and the source and target of the Galois map. -/

@[expose] public section

noncomputable section

section

variable (R K L B : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
  [IsIntegralClosure B R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K L

example : Function.Bijective (Module.Dual.eval R B) := by
  let := IsIntegralClosure.finite R K L B
  let := IsIntegralClosure.isReflexive R K L B
  exact Module.bijective_dual_eval R B

example {ι : Type*} [Finite ι] : Module.IsReflexive R (ι → B) := by
  let := IsIntegralClosure.finite R K L B
  let := IsIntegralClosure.isReflexive R K L B
  infer_instance

example : Module.IsTorsionFree R (Module.End R B) := by
  let := IsIntegralClosure.finite R K L B
  let := IsIntegralClosure.isReflexive R K L B
  infer_instance

end
