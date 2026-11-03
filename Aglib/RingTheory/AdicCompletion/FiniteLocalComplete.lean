/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteModule
public import Aglib.RingTheory.AdicCompletion.FiniteLocalCofinality

/-!
# Maximal-adic completeness of finite local algebras

Finite-module completeness gives completeness for the original extended base
ideal. The existing finite-local ideal comparison then gives completeness for
the original upper maximal ideal, without any new completion construction.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsAdicComplete

/-- A finite local algebra over a complete Noetherian local ring is complete
for its own maximal ideal. The coefficient map is the original local map. -/
theorem maximalIdeal_of_finite_local
    (R C : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing C] [IsLocalRing C] [Algebra R C] [Module.Finite R C]
    [IsLocalHom (algebraMap R C)] : IsAdicComplete (maximalIdeal C) C := by
  let I : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let : IsAdicComplete I C := IsAdicComplete.map_algebraMap_of_finite R (maximalIdeal R) C
  let e := AdicCompletion.finiteLocalAlgEquiv (R := R) (A := C)
  have he : (fun c : C => e (AdicCompletion.of I C c)) =
      AdicCompletion.of (maximalIdeal C) C := by
    funext c
    exact e.commutes c
  apply AdicCompletion.of_bijective_iff.mp
  exact he ▸ e.bijective.comp (AdicCompletion.of_bijective I C)

end IsAdicComplete
