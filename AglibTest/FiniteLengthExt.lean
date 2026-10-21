/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.RegularLocalRing.FiniteLengthExt
import Aglib.RingTheory.Support.FiniteLengthDetection

/-! Actual Ext vanishing and mixed-universe support interfaces. -/

open CategoryTheory Abelian

universe u v

example (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) :=
  Module.support_subset_closedPoint_of_isFiniteLength hM

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) (hd : ringKrullDim R = 3) :
    Subsingleton (Ext N (ModuleCat.of R R) 2) :=
  IsRegularLocalRing.subsingleton_ext_of_isFiniteLength R N hN 3 hd 2 (by decide)

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) (hd : ringKrullDim R = 3) :
    Subsingleton (Ext N (ModuleCat.of R R) 1) :=
  IsRegularLocalRing.subsingleton_ext_of_isFiniteLength R N hN 3 hd 1 (by decide)

example (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsFiniteLength R M ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) :=
  Module.isFiniteLength_iff_support_subset_closedPoint M
