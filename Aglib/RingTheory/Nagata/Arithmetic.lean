/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Localization
public import Aglib.RingTheory.Nagata.FiniteTypeField
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.CharP.Algebra

/-!
# Arithmetic Nagata coefficient rings

Characteristic-zero trace finiteness gives the Japanese condition for normal Noetherian
rings. In dimension one the other prime quotients are fields. Consequently every localization
of the integers is Nagata, including the zero localization. No finite-type ascent theorem
for arithmetic coefficient rings is asserted here.

Reference: Stacks Project, Proposition 10.162.16 (tag 0335).
-/

@[expose] public noncomputable section

universe u

/-- Trace-dual finiteness applies to every finite fraction-field extension in characteristic
zero. The tested extension and original integral closure are retained. -/
theorem IsJapaneseRing.of_isIntegrallyClosed_charZero (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] :
    IsJapaneseRing.{u, 0} R := by
  intro L hL hFL hRL hT hfin
  exact IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)

/-- A characteristic-zero Dedekind domain is Nagata: the zero prime uses trace finiteness,
while each nonzero prime quotient is a field. -/
theorem IsNagataRing.of_isDedekindDomain_charZero (R : Type u)
    [CommRing R] [IsDedekindDomain R] [CharZero R] : IsNagataRing.{u, 0} R := by
  refine ⟨inferInstance, ?_⟩
  intro p hp
  by_cases h : p = ⊥
  · subst p
    exact (IsJapaneseRing.of_isIntegrallyClosed_charZero R).of_ringEquiv
      (RingEquiv.quotientBot R).symm
  · let : p.IsMaximal := hp.isMaximal h
    let := Ideal.Quotient.field p
    exact IsJapaneseRing.of_field (R ⧸ p)

/-- The integers are Nagata without any finite-type stability premise. -/
theorem IsNagataRing.int : IsNagataRing.{0, 0} ℤ :=
  IsNagataRing.of_isDedekindDomain_charZero ℤ

/-- Every localization of the integers is Nagata; no nontriviality is assumed. -/
theorem IsNagataRing.of_isLocalization_int (S : Type) [CommRing S] [Algebra ℤ S]
    (M : Submonoid ℤ) [IsLocalization M S] : IsNagataRing.{0, 0} S :=
  IsNagataRing.of_isLocalization M IsNagataRing.int

/-- Inverting any integer gives a Nagata ring, even when the integer is zero. -/
theorem IsNagataRing.int_away (n : ℤ) :
    IsNagataRing.{0, 0} (Localization.Away n) :=
  IsNagataRing.of_isLocalization_int (Localization.Away n) (Submonoid.powers n)
