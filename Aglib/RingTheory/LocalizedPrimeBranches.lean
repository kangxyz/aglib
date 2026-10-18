/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Original local rings after localization of the base

A prime over the chosen base prime survives localization at the image of its
complement. Its second localization is the original local ring, not a chosen
isomorphic valuation model.
-/

@[expose] public noncomputable section

namespace Localization

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime]

omit [q.IsPrime] in
/-- A prime over `p` avoids the actual denominators for localization of the base. -/
theorem disjoint_basePrimeCompl (hq : q.under A = p) :
    Disjoint ((p.primeCompl.map (algebraMap A S) : Submonoid S) : Set S) q := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ hqmem
  apply ha
  rw [← hq]
  exact hqmem

/-- The extended prime contracts to the original prime, literally. -/
theorem under_map_basePrimeCompl (hq : q.under A = p) :
    (q.map (algebraMap S (Localization (p.primeCompl.map (algebraMap A S))))).under S = q :=
  IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance
    (disjoint_basePrimeCompl p q hq)

/-- Extension along the base localization preserves every prime over `p`. -/
theorem isPrime_map_basePrimeCompl (hq : q.under A = p) :
    (q.map (algebraMap S (Localization (p.primeCompl.map (algebraMap A S))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint _ _ q inferInstance
    (disjoint_basePrimeCompl p q hq)

/-- Localizing the actual extended prime recovers the original local ring. -/
def atPrimeBasePrimeComplEquiv (hq : q.under A = p) :
    letI := isPrime_map_basePrimeCompl p q hq
    Localization.AtPrime
      (q.map (algebraMap S (Localization (p.primeCompl.map (algebraMap A S))))) ≃ₐ[S]
      Localization.AtPrime q := by
  letI := isPrime_map_basePrimeCompl p q hq
  let B := Localization (p.primeCompl.map (algebraMap A S))
  let Q := q.map (algebraMap S B)
  have h : Q.under S = q := under_map_basePrimeCompl p q hq
  letI : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have H := IsLocalization.isLocalization_atPrime_localization_atPrime
      (p.primeCompl.map (algebraMap A S)) Q
    change IsLocalization (Q.under S).primeCompl (Localization.AtPrime Q) at H
    change IsLocalization q.primeCompl (Localization.AtPrime Q)
    simpa only [h] using H
  exact IsLocalization.algEquiv q.primeCompl _ _

/-- The constructed equivalence preserves every map to the original fraction
field (and, more generally, to any `S`-algebra). -/
theorem atPrime_basePrimeCompl_equiv_comp (hq : q.under A = p)
    {E : Type*} [CommRing E] [Algebra S E] :
    let := isPrime_map_basePrimeCompl p q hq
    ∀ (f : Localization.AtPrime
        (q.map (algebraMap S (Localization (p.primeCompl.map (algebraMap A S))))) →ₐ[S] E)
      (g : Localization.AtPrime q →ₐ[S] E),
      g.comp (atPrimeBasePrimeComplEquiv p q hq).toAlgHom = f := by
  let := isPrime_map_basePrimeCompl p q hq
  dsimp only
  intro f g
  let B := Localization (p.primeCompl.map (algebraMap A S))
  let Q := q.map (algebraMap S B)
  have h : Q.under S = q := under_map_basePrimeCompl p q hq
  let : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have H := IsLocalization.isLocalization_atPrime_localization_atPrime
      (p.primeCompl.map (algebraMap A S)) Q
    change IsLocalization (Q.under S).primeCompl (Localization.AtPrime Q) at H
    change IsLocalization q.primeCompl (Localization.AtPrime Q)
    simpa only [h] using H
  apply IsLocalization.algHom_ext q.primeCompl
  ext

/-- The literal localization map between the original local rings. -/
@[instance_reducible]
def basePrimeLocalAlgebra (hq : q.under A = p) :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  letI : q.LiesOver p := ⟨hq.symm⟩
  Localization.AtPrime.algebraOfLiesOver p q

/-- The original domain map factors through the actual local base map. -/
theorem basePrimeLocalTower (hq : q.under A = p) :
    letI := basePrimeLocalAlgebra p q hq
    IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) := by
  let : q.LiesOver p := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  change IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q)
  infer_instance

/-- The literal map of original local rings is local. -/
theorem basePrimeLocal_isLocalHom (hq : q.under A = p) :
    letI := basePrimeLocalAlgebra p q hq
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  let : q.LiesOver p := ⟨hq.symm⟩
  change IsLocalHom (Localization.localRingHom p q (algebraMap A S) hq.symm)
  infer_instance

/-- An equivalence preserving the original domain also preserves its localized
base map. This supplies the base compatibility for the branch equivalence. -/
theorem algEquiv_comp_localizedBase
    {T U : Type*} [CommRing T] [CommRing U]
    [Algebra S T] [Algebra S U] [Algebra A T] [Algebra A U]
    [IsScalarTower A S T] [IsScalarTower A S U]
    [Algebra (Localization.AtPrime p) T] [Algebra (Localization.AtPrime p) U]
    [IsScalarTower A (Localization.AtPrime p) T]
    [IsScalarTower A (Localization.AtPrime p) U] (e : T ≃ₐ[S] U) :
    e.toRingHom.comp (algebraMap (Localization.AtPrime p) T) =
      algebraMap (Localization.AtPrime p) U := by
  apply IsLocalization.ringHom_ext p.primeCompl
  ext a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  change e (algebraMap A T a) = algebraMap A U a
  rw [IsScalarTower.algebraMap_apply A S T, e.commutes,
    ← IsScalarTower.algebraMap_apply A S U]

end Localization
