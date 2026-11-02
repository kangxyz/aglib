/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.FiniteTypeField
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-! # Local models in the original finite field extension

The ring is the localization of the literal integral closure at a prime over
the prescribed base prime. Its fraction field is the supplied extension field,
through the canonical localization map. No replacement field or normalization
is chosen, and no separability is assumed. The local ring is not asserted to
be finite over the base; only the unlocalized integral closure is finite.
-/

@[expose] public noncomputable section

universe u

namespace integralClosure

variable (R K L : Type u) [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L]

/-- The original localization maps to the supplied extension field. -/
def localModelToField (q : Ideal (integralClosure R L)) [q.IsPrime] :
    Localization.AtPrime q →ₐ[integralClosure R L] L := by
  let : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  exact Localization.mapToFractionRing L q.primeCompl (Localization.AtPrime q)
    q.primeCompl_le_nonZeroDivisors

/-- The canonical map retains the literal inclusion of integral elements. -/
theorem localModelToField_algebraMap (q : Ideal (integralClosure R L)) [q.IsPrime]
    (c : integralClosure R L) :
    localModelToField R K L q (algebraMap _ (Localization.AtPrime q) c) = c :=
  (localModelToField R K L q).commutes c

/-- Localizing the original integral closure retains exactly the supplied
fraction field and its original scalar triangle. -/
theorem localModel_isFractionRing (q : Ideal (integralClosure R L)) [q.IsPrime] :
    letI := (localModelToField R K L q).toRingHom.toAlgebra
    IsFractionRing (Localization.AtPrime q) L := by
  let : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let := (localModelToField R K L q).toRingHom.toAlgebra
  let : IsScalarTower (integralClosure R L) (Localization.AtPrime q) L :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((localModelToField R K L q).commutes c).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl
    (Localization.AtPrime q) L

/-- A prescribed prime of a finite-type field domain has a normal Noetherian
local model in the original finite field extension. The local structural map
and its coefficient triangle are the native maps. A natural number outside
the original prime remains a unit, with no separability assumption. -/
theorem exists_localModel_of_finiteType_field
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (p : Ideal R) [p.IsPrime] (n : ℕ) (hn : (n : R) ∉ p) :
    ∃ (q : Ideal (integralClosure R L)) (hq : q.IsPrime),
      letI := hq
      ∃ (hqp : q.under R = p),
      IsNoetherianRing (Localization.AtPrime q) ∧
      IsIntegrallyClosed (Localization.AtPrime q) ∧
      IsLocalRing (Localization.AtPrime q) ∧
      IsDomain (Localization.AtPrime q) ∧
      IsUnit (n : Localization.AtPrime q) ∧
      IsLocalHom (Localization.localRingHom p q (algebraMap R (integralClosure R L))
        hqp.symm) ∧
      (∀ r : R,
        Localization.localRingHom p q (algebraMap R (integralClosure R L)) hqp.symm
          (algebraMap R (Localization.AtPrime p) r) =
            algebraMap R (Localization.AtPrime q) r) ∧
      (letI := (localModelToField R K L q).toRingHom.toAlgebra
       IsFractionRing (Localization.AtPrime q) L) := by
  let C := integralClosure R L
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : Module.Finite R C :=
    IsJapaneseRing.finite_integralClosure_of_finiteType_field k R K L
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hinj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    have h := congrArg (algebraMap C L) hab
    simpa only [← IsScalarTower.algebraMap_apply] using h
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := C) p (by
      intro r hr
      have hz : r = 0 := hinj (hr.trans (map_zero (algebraMap R C)).symm)
      simpa only [hz] using p.zero_mem)
  let := hq
  let : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  have hnq : (n : C) ∉ q := by
    intro h
    apply hn
    rw [← hqp]
    change algebraMap R C (n : R) ∈ q
    simpa only [map_natCast] using h
  have hunit : IsUnit (n : Localization.AtPrime q) := by
    simpa only [map_natCast] using
      (IsLocalization.map_units (Localization.AtPrime q)
        (⟨(n : C), hnq⟩ : q.primeCompl))
  refine ⟨q, hq, hqp, inferInstance, inferInstance, inferInstance, inferInstance,
    hunit, inferInstance, ?_, localModel_isFractionRing R K L q⟩
  intro r
  exact (Localization.localRingHom_to_map p q (algebraMap R C) hqp.symm r).trans
    (IsScalarTower.algebraMap_apply R C (Localization.AtPrime q) r).symm

end integralClosure
