/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Defs
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Japanese rings under the original fraction-field and ring comparisons

The fraction-field comparison changes only the intermediate coefficient
action. The ambient field and its original base-ring action are unchanged.
Ring equivalences transfer the Japanese condition, and the actual zero
prime quotient gives the Japanese condition of a Nagata domain.

All rings and fields lie in one ambient universe. These statements use
the existing predicates at auxiliary universe zero; no universe-invariance
theorem is asserted.
-/

@[expose] public noncomputable section

universe u

/-- Apply the Japanese condition through any supplied fraction field,
retaining the same extension field and its original base-ring action. -/
theorem IsJapaneseRing.finite_integralClosure_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] (h : IsJapaneseRing.{u, 0} R)
    (K L : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] : Module.Finite R (integralClosure R L) := by
  let e := IsLocalization.algEquiv (R := R) (nonZeroDivisors R) (FractionRing R) K
  let : Algebra (FractionRing R) L :=
    ((algebraMap K L).comp e.toRingHom).toAlgebra
  let : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R L r = algebraMap K L (e (algebraMap R (FractionRing R) r))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply R K L r
  let : FiniteDimensional (FractionRing R) L :=
    Module.Finite.of_equiv_equiv e.toRingEquiv.symm (RingEquiv.refl L) (by
      ext x
      change algebraMap K L (e (e.symm x)) = algebraMap K L x
      rw [e.apply_symm_apply])
  exact h L

/-- A ring equivalence transports the Japanese condition in the same
ambient universe. Each extension field retains its original target action. -/
theorem IsJapaneseRing.of_ringEquiv
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (h : IsJapaneseRing.{u, 0} R) (e : R ≃+* S) : IsJapaneseRing.{u, 0} S := by
  intro L hL hFL hSL hT hfin
  let : Algebra R S := e.toRingHom.toAlgebra
  let : IsFractionRing R (FractionRing S) :=
    IsFractionRing.of_ringEquiv_left e
      (IsScalarTower.algebraMap_apply R S (FractionRing S))
  let : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R (FractionRing S) L :=
    IsScalarTower.to₁₃₄ R S (FractionRing S) L
  let : Module.Finite R S := RingHom.Finite.of_surjective e.toRingHom e.surjective
  let : Algebra.IsIntegral R S := inferInstance
  let : Module.Finite R (integralClosure R L) :=
    h.finite_integralClosure_of_isFractionRing (FractionRing S) L
  let : Module.Finite R (integralClosure S L) :=
    Module.Finite.equiv (integralClosure.equivOfIntegral R S L).symm.toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite R S (integralClosure S L)

/-- The zero-prime clause of the Nagata condition gives the Japanese
condition of the original domain, through its actual zero-quotient equivalence. -/
theorem IsNagataRing.isJapaneseRing
    {R : Type u} [CommRing R] [IsDomain R] (h : IsNagataRing.{u, 0} R) :
    IsJapaneseRing.{u, 0} R :=
  (h.isJapaneseRing_quotient (⊥ : Ideal R)).of_ringEquiv (RingEquiv.quotientBot R)
