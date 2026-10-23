/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Japanese domains and Nagata rings

The Japanese property is finiteness of the literal integral closure in every
finite extension of the canonical fraction field. The original coefficient
action is retained through its scalar tower. Nagata means Noetherian and
Japanese at every actual prime quotient.

The auxiliary universe `v` is part of the interface: extension fields over a
ring in `Type u` are tested in `Type (max u v)`. No change-of-universe theorem
or finite-type stability theorem is included in these definitions.

Source: Stacks, Definitions 10.161.1 and 10.162.1.
-/

@[expose] public section

universe u v

/-- A domain is Japanese, or N-2, if its literal integral closure is finite
in every finite extension of its canonical fraction field in the test universe. -/
def IsJapaneseRing (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type (max u v)) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L],
    Module.Finite R (integralClosure R L)

/-- A Nagata ring is Noetherian and every prime quotient is Japanese,
with the same explicit auxiliary extension-field universe. -/
def IsNagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
  ∀ (p : Ideal R) [p.IsPrime], IsJapaneseRing.{u, v} (R ⧸ p)

/-- The Japanese condition applies to the original field and coefficient map. -/
theorem IsJapaneseRing.finite_integralClosure
    {R : Type u} [CommRing R] [IsDomain R] (h : IsJapaneseRing.{u, v} R)
    (L : Type (max u v)) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L) := h L

/-- Noetherianity is an explicit component of the Nagata condition. -/
theorem IsNagataRing.isNoetherianRing
    {R : Type u} [CommRing R] (h : IsNagataRing.{u, v} R) :
    IsNoetherianRing R := h.1

/-- Every actual prime quotient of a Nagata ring is Japanese. -/
theorem IsNagataRing.isJapaneseRing_quotient
    {R : Type u} [CommRing R] (h : IsNagataRing.{u, v} R)
    (p : Ideal R) [p.IsPrime] : IsJapaneseRing.{u, v} (R ⧸ p) := h.2 p
