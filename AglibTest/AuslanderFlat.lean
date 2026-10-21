/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Reflexive.AuslanderFlat

/-! The global conclusion needs neither a local base ring nor a global free module. -/

universe u

example (R M : Type u) [CommRing R] [IsRegularRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M)) : Module.Flat R M :=
  ModuleCat.flat_of_endomorphism_equiv_of_isRegularRing R (ModuleCat.of R M) r e
