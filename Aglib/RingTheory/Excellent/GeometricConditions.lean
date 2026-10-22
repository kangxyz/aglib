/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Order.RelSeries
public import Mathlib.Order.Cover

/-! # The regular locus, J-2, and universal catenarity

The auxiliary universe parameter in the finite-type tests is part of the interface.
Test algebras live in `Type (max u v)`, never below the base universe `u`.
No change-of-universe theorem for these predicates is assumed here.
-/

@[expose] public section

universe u v

/-- The points whose actual localizations are regular local rings. -/
def PrimeSpectrum.regularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- J-2, with finite-type test algebras in the explicit universe `max u v`. -/
def IsJ2Ring (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
  ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
    IsOpen (PrimeSpectrum.regularLocus B)

/-- A saturated finite chain in the prime spectrum. Covering is in the poset of
prime ideals, not in the larger poset of all ideals. -/
abbrev PrimeSpectrum.SaturatedChain (R : Type u) [CommRing R] :=
  RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q}

/-- A Noetherian ring is catenary when saturated prime chains with the same
endpoints have the same length. -/
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
  ∀ c d : PrimeSpectrum.SaturatedChain R,
    c.head = d.head → c.last = d.last → c.length = d.length

/-- Universal catenarity, testing finite-type algebras in universe `max u v`. -/
def IsUniversallyCatenaryRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
  ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
    IsCatenaryRing B
