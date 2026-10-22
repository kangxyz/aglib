/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.BaseChange
public import Mathlib.RingTheory.Etale.Kaehler

/-! # Differential Fitting ideals under formally étale changes

The coefficient comparison is the actual map in the Jacobi–Zariski sequence.
The algebra comparison is the native formally étale differential base change.
Evaluation commutes with these comparisons along the specified point square.
-/

@[expose] public noncomputable section

namespace KaehlerDifferential

section Coefficients

variable (R A T : Type*) [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra R T] [Algebra A T] [IsScalarTower R A T]
  [Algebra.FormallyUnramified R A]

/-- Enlarging the coefficient ring through a formally unramified map leaves the
relative differential module unchanged. The forward arrow is the canonical map. -/
def coefficientEquivOfFormallyUnramified :
    KaehlerDifferential R T ≃ₗ[T] KaehlerDifferential A T := by
  refine LinearEquiv.ofBijective (KaehlerDifferential.map R A T T)
    ⟨?_, map_surjective R A T⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R A T x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- The coefficient equivalence is literally the Jacobi–Zariski comparison. -/
@[simp] theorem coefficientEquivOfFormallyUnramified_apply
    (x : KaehlerDifferential R T) :
    coefficientEquivOfFormallyUnramified R A T x =
      KaehlerDifferential.map R A T T x := rfl

/-- Formally unramified coefficient extension preserves every differential Fitting ideal. -/
theorem fittingIdeal_coefficient_of_formallyUnramified (k : ℕ) :
    Module.fittingIdeal T (KaehlerDifferential A T) k =
      Module.fittingIdeal T (KaehlerDifferential R T) k :=
  (Module.fittingIdeal_congr (coefficientEquivOfFormallyUnramified R A T) k).symm

end Coefficients

section AlgebraChange

variable (R B T : Type*) [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T] [Algebra B T] [IsScalarTower R B T]
  [Algebra.FormallyEtale B T] [Module.Finite B (KaehlerDifferential R B)]

/-- Formally étale source extension extends the actual relative differential Fitting ideal. -/
theorem fittingIdeal_of_formallyEtale (k : ℕ) :
    Module.fittingIdeal T (KaehlerDifferential R T) k =
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map (algebraMap B T) := by
  rw [← Module.fittingIdeal_congr (tensorKaehlerEquivOfFormallyEtale R B T) k,
    Module.fittingIdeal_baseChange]

end AlgebraChange

section BothChanges

variable (R A B T : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
  [IsScalarTower R A T] [IsScalarTower R B T]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyEtale B T]
  [Module.Finite B (KaehlerDifferential R B)]

/-- Simultaneous unramified coefficient change and formally étale algebra extension
preserve the index and extend the original differential Fitting ideal. -/
theorem fittingIdeal_of_formallyEtale_of_formallyUnramified (k : ℕ) :
    Module.fittingIdeal T (KaehlerDifferential A T) k =
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map (algebraMap B T) := by
  rw [fittingIdeal_coefficient_of_formallyUnramified R A T,
    fittingIdeal_of_formallyEtale R B T]

/-- The actual evaluated Fitting ideals agree along a commuting point square.
No injectivity, domain, or flatness of the evaluation maps is required. -/
theorem map_fittingIdeal_of_formallyEtale_of_formallyUnramified
    {S U : Type*} [CommRing S] [CommRing U]
    (χ : B →+* S) (χ' : T →+* U) (σ : S →+* U)
    (hpoint : χ'.comp (algebraMap B T) = σ.comp χ) (k : ℕ) :
    (Module.fittingIdeal T (KaehlerDifferential A T) k).map χ' =
      ((Module.fittingIdeal B (KaehlerDifferential R B) k).map χ).map σ := by
  rw [fittingIdeal_of_formallyEtale_of_formallyUnramified R A B T,
    Ideal.map_map, hpoint, Ideal.map_map]

end BothChanges

end KaehlerDifferential
