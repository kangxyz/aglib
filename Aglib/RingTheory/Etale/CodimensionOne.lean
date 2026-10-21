/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.IntegralExtension
public import Aglib.RingTheory.Localization.HeightOne
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Source codimension one and finite etale localized models

The source condition is Mathlib's `Algebra.IsUnramifiedAt`, meaning formal
unramifiedness of the source stalk. The finite algebra after localizing the base
is the tensor product, not the localization at an individual source prime.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Algebra

/-- Formal unramifiedness can be checked at maximal ideals of the source. -/
theorem formallyUnramified_of_isUnramifiedAt_maximal
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (q : Ideal B) [q.IsMaximal], IsUnramifiedAt R q) :
    FormallyUnramified R B := by
  apply (formallyUnramified_iff R B).mpr
  apply Module.subsingleton_of_localization_maximal
    (fun q _ ↦ Ω[Localization.AtPrime q⁄R])
    (fun q _ ↦ KaehlerDifferential.map R R B (Localization.AtPrime q))
  intro q hq
  let := h q
  infer_instance

/-- A localization is formally unramified if the original algebra is unramified
at the contractions of all its maximal ideals. No finiteness of source stalks is used. -/
theorem formallyUnramified_localization_of_maximal
    {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
    [Algebra R B] [Algebra B T] [Algebra R T] [IsScalarTower R B T]
    (M : Submonoid B) [IsLocalization M T]
    (h : ∀ (q : Ideal T) [q.IsMaximal], IsUnramifiedAt R (q.under B)) :
    FormallyUnramified R T := by
  apply formallyUnramified_of_isUnramifiedAt_maximal
  intro q hq
  let : IsLocalization.AtPrime (Localization.AtPrime q) (q.under B) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime q) q
  let := h q
  exact FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv (q.under B).primeCompl
      (Localization.AtPrime (q.under B)) (Localization.AtPrime q)).restrictScalars R)

/-- Finite algebras over a normal domain, unramified at height-one source primes,
are formally unramified after base localization at a height-one prime. -/
theorem formallyUnramified_atPrime_tensor_of_height_one
    {R B : Type*} [CommRing R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Module.Finite R B] [IsIntegrallyClosed R]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → IsUnramifiedAt R q.asIdeal)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] B) := by
  let S := Localization.AtPrime p
  let T := S ⊗[R] B
  let : Algebra B T := TensorProduct.rightAlgebra
  have hT : FormallyUnramified R T := by
    apply formallyUnramified_localization_of_maximal (Algebra.algebraMapSubmonoid B p.primeCompl)
    intro q hq
    have hqS : (q.under S).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal q
    have heq : (q.under B).under R = p := by
      rw [Ideal.under_under, ← Ideal.under_under (B := S),
        IsLocalRing.eq_maximalIdeal hqS]
      exact IsLocalization.AtPrime.under_maximalIdeal S p
    apply h ⟨q.under B, inferInstance⟩
    rw [Ideal.height_eq_height_under_of_normal (R := R), heq, hp]
  let := hT
  exact FormallyUnramified.of_restrictScalars R S T

/-- A finite faithful domain algebra unramified at height-one source primes has
an etale finite model at each height-one base localization. -/
theorem etale_atPrime_tensor_of_height_one
    {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [CommRing B] [IsDomain B] [Algebra R B]
    [FaithfulSMul R B] [Module.Finite R B]
    (h : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 → IsUnramifiedAt R q.asIdeal)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] B) := by
  let S := Localization.AtPrime p
  let T := S ⊗[R] B
  let : IsDedekindDomain S :=
    IsLocalization.AtPrime.isDedekindDomain_of_height_le_one p S hp.le
  let : Module.IsTorsionFree S T :=
    IsLocalizedModule.isTorsionFree (TensorProduct.mk R S B 1) p.primeCompl
  let : Module.Flat S T := inferInstance
  let : FormallyUnramified S T := formallyUnramified_atPrime_tensor_of_height_one h p hp
  let : FinitePresentation S T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Etale.of_formallyUnramified_of_flat

end Algebra
