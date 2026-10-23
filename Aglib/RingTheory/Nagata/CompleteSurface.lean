/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Defs
public import Aglib.RingTheory.IntegralClosure.CompleteSurface.PrimeQuotient

/-!
# Complete normal local surfaces are Nagata

Every prime quotient of the original complete Noetherian normal local
domain of dimension at most two has finite normalization in every finite
fraction-field extension. Applying that proved supplier to the canonical
fraction field of each literal quotient gives the Nagata condition.

The result includes inseparable extensions and retains the auxiliary test
universe. It does not assert finite-type or localization stability.
-/

@[expose] public section

universe u v

/-- A complete Noetherian normal local domain of dimension at most two is
Nagata in every explicit auxiliary extension-field universe. -/
theorem IsNagataRing.of_complete_local_normal_dimLE_two
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsLocalRing R] [Ring.KrullDimLE 2 R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsNagataRing.{u, v} R := by
  refine ⟨inferInstance, ?_⟩
  intro p hp L hL hKL hRL hT hfin
  exact integralClosure.finite_primeQuotient_of_complete_local_normal_dimLE_two
    R p (FractionRing (R ⧸ p)) L
