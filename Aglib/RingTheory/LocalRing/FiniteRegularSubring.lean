/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.FiniteCompleteRegularSubring

/-! # Dimension-two compatibility for the general finite regular subring construction -/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

universe u

/-- Every complete Noetherian local domain of dimension two admits an
actual finite injective local map from a complete regular local domain
of dimension two, including arbitrary equal and mixed characteristics. -/
theorem exists_finite_complete_regular_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (hd : ringKrullDim A = 2) :
    ∃ (R : CommRingCat.{u}) (hR : IsRegularLocalRing R),
      let _ : IsRegularLocalRing R := hR
      IsDomain R ∧ IsAdicComplete (maximalIdeal R) R ∧ ringKrullDim R = 2 ∧
        ∃ f : R →+* A, Function.Injective f ∧ IsLocalHom f ∧
          (let _ : Algebra R A := f.toAlgebra; Module.Finite R A) := by
  exact exists_finite_complete_regular_subring_of_dimension A 2 hd

end IsLocalRing
