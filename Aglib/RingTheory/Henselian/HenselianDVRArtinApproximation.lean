/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselianNativeGeometricEquiv
public import Aglib.RingTheory.Henselian.DVRGeometricLocalArtinApproximation
public import Aglib.RingTheory.AdicCompletion.RingEquivApproximation

/-!
# Artin approximation in an actually henselian DVR

The coefficient ring itself contains the exact solution. Both the finite
quotient equation and extended ideal-power error refer to its original
I-adic completion, not an abstractly isomorphic surrogate.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace HenselianLocalRing

universe u w t e

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [CharZero R]

/-- Native-ring approximation for a henselian DVR, at every proper ideal,
with independent finite equation and unknown universes and both original
precision conclusions. -/
theorem exists_solution_ideal_completion_with_precision_of_charZeroDVR
    (I : Ideal R) (hI : I ≠ ⊤)
    {σ : Type w} {ι : Type t} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ R) (y : σ → AdicCompletion I R)
    (hy : ∀ i, eval₂ (algebraMap R (AdicCompletion I R)) y (F i) = 0)
    (c : ℕ) :
    ∃ x : σ → R,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap R (AdicCompletion I R) (x j) - y j ∈
        (I ^ c).map (algebraMap R (AdicCompletion I R)) := by
  let e := Henselization.nativeGeometricEquiv R
  have hJ : I.map e.toRingHom ≠ ⊤ := AdicCompletion.map_ne_top_of_ringEquiv e I hI
  refine AdicCompletion.exists_solution_of_ringEquiv_solver e I ?_ F y hy c
  intro E s hs d
  exact GeometricLocalHenselization.exists_solution_ideal_completion_with_precision_of_charZeroDVR
    R R (maximalIdeal R) (I.map e.toRingHom) hJ E s hs d

end HenselianLocalRing
