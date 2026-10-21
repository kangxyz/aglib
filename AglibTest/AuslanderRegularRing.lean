/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.Reflexive.AuslanderRegularRing

/-! Consumers of the local regular-ring Auslander criterion on the actual module carrier. -/

noncomputable section

universe u

example (R M : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M)) : Module.Free R M :=
  ModuleCat.free_of_endomorphism_equiv_of_isRegularRing R (ModuleCat.of R M) r e

example (R M : Type u) [CommRing R] [IsRegularRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (e : Module.End R M ≃ₗ[R] (Fin r → M)) (p : Ideal R) [p.IsPrime] :
    Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
  ModuleCat.free_localizedModule_of_endomorphism_equiv_of_isRegularRing
    R (ModuleCat.of R M) r e p
