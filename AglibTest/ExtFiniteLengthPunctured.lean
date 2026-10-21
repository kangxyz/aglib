/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.Algebra.Category.ModuleCat.Ext.FiniteLength

open CategoryTheory Abelian

universe u

example (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (Ext M (ModuleCat.of R R) 1) :=
  ModuleCat.isFiniteLength_ext_one_of_free_punctured R M hM

example (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    Module.support R (Ext M (ModuleCat.of R R) 1) ⊆
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) :=
  Module.support_subset_closedPoint_of_isFiniteLength
    (ModuleCat.isFiniteLength_ext_one_of_projective_punctured R M hM)
