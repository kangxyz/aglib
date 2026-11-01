/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Flatness of the original finite-variable power-series algebra

Only the polynomial variable ideal is completed in the proof. The coefficient
ring need not be local or complete.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- Finite-variable power series are flat over the original Noetherian coefficient ring. -/
theorem flat_of_isNoetherian (σ A : Type*) [Finite σ] [CommRing A] [IsNoetherianRing A] :
    Module.Flat A (MvPowerSeries σ A) := by
  let : Module.Flat A
      (AdicCompletion (MvPolynomial.idealOfVars σ A) (MvPolynomial σ A)) :=
    Module.Flat.trans A (MvPolynomial σ A) _
  exact Module.Flat.of_linearEquiv
    ((toAdicCompletionAlgEquiv σ A).restrictScalars A).toLinearEquiv

end MvPowerSeries
