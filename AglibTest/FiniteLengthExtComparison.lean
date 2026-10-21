/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtComparison

noncomputable section

open CategoryTheory Abelian

universe u

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {D E : ModuleCat.{u} R} (e : D ⟶ E)
    (hker : IsFiniteLength R (LinearMap.ker e.hom))
    (hcoker : IsFiniteLength R (E ⧸ LinearMap.range e.hom))
    (hd : ringKrullDim R = 3) :
    Ext E (ModuleCat.of R R) 1 ≃ₗ[R] Ext D (ModuleCat.of R R) 1 :=
  IsRegularLocalRing.extOneLinearEquivOfIsFiniteLength R e hker hcoker 3 hd le_rfl

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {D E : ModuleCat.{u} R} (e : D ⟶ E)
    (hker : IsFiniteLength R (LinearMap.ker e.hom))
    (hcoker : IsFiniteLength R (E ⧸ LinearMap.range e.hom))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h3 : 3 ≤ d)
    (x : Ext E (ModuleCat.of R R) 1) :
    IsRegularLocalRing.extOneLinearEquivOfIsFiniteLength R e hker hcoker d hd h3 x =
      (Ext.mk₀ e).comp x (zero_add 1) := rfl
