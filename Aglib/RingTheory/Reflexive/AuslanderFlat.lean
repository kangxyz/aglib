/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.AuslanderRegularRing
public import Mathlib.RingTheory.Flat.Localization

/-!
# Global flatness from the Auslander endomorphism criterion

The local free criterion applies to every maximal localization of the actual
module. Flatness then descends by the native maximal-localization criterion.
The conclusion is flatness, not global freeness.
-/

@[expose] public section

noncomputable section

universe u

namespace ModuleCat

/-- A finite reflexive module over a regular ring is flat if its endomorphism
module is a finite power of itself. -/
theorem flat_of_endomorphism_equiv_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M)) : Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro p hp
  let : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    free_localizedModule_of_endomorphism_equiv_of_isRegularRing R M r eEnd p
  let : Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Flat.of_free
  exact Module.Flat.trans R (Localization.AtPrime p) (LocalizedModule p.primeCompl M)

end ModuleCat
