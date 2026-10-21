/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismUnramified
public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismFin
public import Aglib.RingTheory.IntegralClosure.NormalClosureDescent
public import Aglib.RingTheory.Reflexive.AuslanderFlat
public import Aglib.RingTheory.IntegralClosure.NormalClosureFlat
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Algebraic Zariski–Nagata purity with an explicit separable fraction-field model

The original finite normal algebra is retained in the conclusion. The proof
uses the actual normal closure inside the separable closure of the base fraction
field, reconstructs its coefficient endomorphisms, applies the Auslander flat
criterion, then finite-flat purity and descent. No flatness, reflexivity,
endomorphism decomposition or upper-normalization etaleness is an input.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra

/-- A finite normal domain algebra over a regular domain is etale if its
specified finite separable fraction-field extension is unramified at every
height-one prime of the original source. -/
theorem etale_of_unramified_height_one_of_isRegularRing
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularRing A]
    (B : Type v) [CommRing B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B]
    (E : Type w) [Field E] [Algebra B E] [IsFractionRing B E]
    [Algebra A E] [IsScalarTower A B E]
    [Algebra (FractionRing A) E] [IsScalarTower A (FractionRing A) E]
    [Algebra.IsSeparable (FractionRing A) E]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → IsUnramifiedAt A q.asIdeal) :
    Etale A B := by
  classical
  let : IsIntegrallyClosed A := IsIntegrallyClosed.of_localization_maximal
    (fun p _ _ => IsRegularLocalRing.isIntegrallyClosed_of_regularLocal (Localization.AtPrime p))
  let : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) E :=
    IsIntegralClosure.isLocalization A (FractionRing A) E B
  let : FiniteDimensional (FractionRing A) E :=
    Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  let K := FractionRing A
  let Ω := SeparableClosure K
  let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq' rfl
  let N := IntermediateField.normalClosure K E Ω
  let C := integralClosure A N
  let : Module.Finite A C := IsIntegralClosure.finite A K N C
  let : Module.IsReflexive A C := IsIntegralClosure.isReflexive A K N C
  have hc := IsIntegralClosure.unramified_height_one_normalization A B E h
  let eEnd := IsIntegralClosure.galoisEndomorphismFinEquiv A K N C
    (integralClosure.normalClosure_galoisEndomorphism_surjective A K E Ω hc)
  let : Module.Flat A C := ModuleCat.flat_of_endomorphism_equiv_of_isRegularRing
    A (ModuleCat.of A C) (Fintype.card (N ≃ₐ[K] N)) eEnd
  let : Etale A C := integralClosure.normalClosure_etale_of_flat A E Ω hc
  let : Nonempty (E →ₐ[K] Ω) := ⟨IsSepClosed.lift⟩
  exact etale_of_normalClosure_normalization A B K E Ω

end Algebra

namespace Algebra

section FractionFields

attribute [local instance] FractionRing.liftAlgebra

/-- Algebraic Zariski–Nagata purity for the canonical fraction fields of the
original regular base and finite normal source. The fraction-field algebra is
induced by the faithful original algebra map. -/
theorem etale_of_unramified_height_one
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → IsUnramifiedAt A q.asIdeal) :
    Etale A B :=
  etale_of_unramified_height_one_of_isRegularRing A B (FractionRing B) h

end FractionFields

end Algebra
