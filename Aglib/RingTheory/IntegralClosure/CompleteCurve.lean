/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteGeneration
public import Aglib.RingTheory.AdicCompletion.FiniteModule
public import Aglib.RingTheory.FiniteLength.ScalarQuotient
public import Aglib.RingTheory.IntegralClosure.Colength
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Finite normalization of complete local curves

An integral domain algebra with torsion-free base action and finite rank
over a Noetherian domain of dimension at most one is Noetherian. If the
base is complete and local, that algebra is finite. Applied to the literal
integral closure, whose base action is injective, this gives finite
normalization in every finite fraction-field extension, without
separability assumptions.

For a reduced complete Noetherian local base of dimension at most one, the literal
normalization in its total quotient ring embeds in the finite product of
the normalizations of the actual minimal-prime quotients. This proves
finite normalization and finite colength for the original coefficient map.
-/

@[expose] public section

open scoped Pointwise nonZeroDivisors

namespace Algebra.IsIntegral

variable {R B : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R] [CommRing B] [IsDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] [Module.IsTorsionFree R B]

/-- The integral-algebra case of Krull--Akizuki with a torsion-free base
action, using finite rank without a separability or module-finiteness
assumption. -/
theorem isNoetherianRing_of_rank_lt_aleph0
    (hrank : Module.rank R B < Cardinal.aleph0) : IsNoetherianRing B := by
  apply (isNoetherianRing_iff_ideal_fg B).mpr
  intro J
  by_cases hJ : J = ⊥
  · subst J
    exact Submodule.fg_bot
  obtain ⟨a, haJ, ha⟩ := (J.under R).ne_bot_iff.mp (Ideal.IsIntegral.under_ne_bot R hJ)
  let I : Ideal B := Ideal.span {algebraMap R B a}
  have hIJ : I ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr haJ
  have hI : I.restrictScalars R = a • (⊤ : Submodule R B) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map,
      Ideal.map_span, Set.image_singleton]
  have hfinite : IsFiniteLength R (B ⧸ I) := by
    change IsFiniteLength R (B ⧸ I.restrictScalars R)
    rw [hI]
    exact QuotSMulTop.isFiniteLength_of_rank_lt_aleph0 hrank a ha
  let : IsNoetherian R (B ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  let : IsNoetherian B (B ⧸ I) := isNoetherian_of_tower R inferInstance
  apply Submodule.fg_of_fg_map_of_fg_inf_ker I.mkQ
    (IsNoetherian.noetherian _)
  simpa only [Submodule.ker_mkQ, inf_eq_right.mpr hIJ] using
    (Submodule.fg_span_singleton (algebraMap R B a))

/-- Over a complete Noetherian local domain of dimension at most one,
an integral domain algebra of finite rank is finite over the original
coefficient ring when its base action is torsion-free. The target's
completeness is not assumed. -/
theorem finite_of_isAdicComplete_maximalIdeal [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hrank : Module.rank R B < Cardinal.aleph0) : Module.Finite R B := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · let : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    exact Module.rank_lt_aleph0_iff.mp hrank
  obtain ⟨a, ham, ha⟩ := (IsLocalRing.maximalIdeal R).ne_bot_iff.mp hm
  let : IsNoetherianRing B := isNoetherianRing_of_rank_lt_aleph0 hrank
  have hfinite := QuotSMulTop.isFiniteLength_of_rank_lt_aleph0 hrank a ha
  let : IsNoetherian R (QuotSMulTop a B) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  have hquot : a • (⊤ : Submodule R B) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R B) := by
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal R)).mpr ham)
  let : Module.Finite R
      (B ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R B))) :=
    Module.Finite.of_surjective (Submodule.factor hquot) (Submodule.factor_surjective hquot)
  apply Module.finite_of_isPrecomplete_of_le_jacobson (IsLocalRing.maximalIdeal R)
  apply le_sInf
  rintro J ⟨_, hJ⟩
  let : J.IsMaximal := hJ
  apply Ideal.map_le_iff_le_comap.mpr
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) J)).symm.le

end Algebra.IsIntegral

namespace integralClosure

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R] [IsLocalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Module.Finite K L]

include K

/-- Finite normalization of a complete Noetherian local domain of dimension
at most one in any finite extension of its fraction field. This includes
purely inseparable extensions. -/
theorem finite_of_complete_local_dimLE_one : Module.Finite R (integralClosure R L) := by
  let : Module.IsTorsionFree R L := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective R K))
  let : Module.IsTorsionFree R (integralClosure R L) :=
    IsIntegralClosure.isTorsionFree R L
  let : Algebra.IsIntegral R (integralClosure R L) := IsIntegralClosure.isIntegral_algebra R L
  apply Algebra.IsIntegral.finite_of_isAdicComplete_maximalIdeal
  apply lt_of_le_of_lt
    ((integralClosure R L).val.toLinearMap.rank_le_of_injective Subtype.val_injective)
  rw [← IsFractionRing.rank_right_eq R K L]
  exact Module.rank_lt_aleph0 K L

end integralClosure

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace integralClosure

section Components

variable (R Q : Type*) [CommRing R] [CommRing Q] [Algebra R Q] [IsFractionRing R Q]

/-- A denominator in the total quotient ring remains nonzero in every
minimal-prime quotient. No reducedness or Noetherianity is needed here. -/
theorem quotient_mk_ne_zero_of_nonZeroDivisor (p : Ideal R)
    (hp : p ∈ minimalPrimes R) (s : R⁰) :
    Ideal.Quotient.mk p (s : R) ≠ 0 := by
  intro hs
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (Ideal.Quotient.eq_zero_iff_mem.mp hs) hp s.property

/-- The actual extension of the minimal-prime quotient map from the total
quotient ring to the fraction field of that quotient. -/
def toMinimalPrimeFraction (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    Q →ₐ[R] FractionRing (R ⧸ p) := by
  let : p.IsPrime := hp.isPrime
  apply IsLocalization.liftAlgHom (M := R⁰) (f := Algebra.ofId R _)
  intro s
  apply isUnit_iff_ne_zero.mpr
  change algebraMap R (FractionRing (R ⧸ p)) (s : R) ≠ 0
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p))]
  intro hs
  apply quotient_mk_ne_zero_of_nonZeroDivisor R p hp s
  apply IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))
  simpa only [Ideal.Quotient.algebraMap_eq, map_zero] using hs

theorem toMinimalPrimeFraction_algebraMap (p : Ideal R) (hp : p ∈ minimalPrimes R) (r : R) :
    toMinimalPrimeFraction R Q p hp (algebraMap R Q r) =
      algebraMap R (FractionRing (R ⧸ p)) r :=
  (toMinimalPrimeFraction R Q p hp).commutes r

/-- The minimal-prime fraction map restricts to the literal normalizations,
with the original `R`-coefficient action on both sides. -/
def toMinimalPrimeNormalization (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    integralClosure R Q →ₐ[R] integralClosure (R ⧸ p) (FractionRing (R ⧸ p)) where
  toFun b := ⟨toMinimalPrimeFraction R Q p hp (b : Q),
    (b.property.map (toMinimalPrimeFraction R Q p hp)).tower_top⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  commutes' r := by
    apply Subtype.ext
    change toMinimalPrimeFraction R Q p hp (algebraMap R Q r) =
      algebraMap R (FractionRing (R ⧸ p)) r
    exact toMinimalPrimeFraction_algebraMap R Q p hp r

@[simp]
theorem coe_toMinimalPrimeNormalization (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (b : integralClosure R Q) :
    (toMinimalPrimeNormalization R Q p hp b : FractionRing (R ⧸ p)) =
      toMinimalPrimeFraction R Q p hp (b : Q) := rfl

/-- The product of the actual minimal-prime fraction maps. -/
def toMinimalPrimeFractions :
    Q →ₐ[R] ∀ p : minimalPrimes R, FractionRing (R ⧸ p.val) :=
  AlgHom.pi fun p ↦ toMinimalPrimeFraction R Q p.val p.property

/-- Reducedness makes the product of the actual fraction maps injective. -/
theorem toMinimalPrimeFractions_injective [IsReduced R] :
    Function.Injective (toMinimalPrimeFractions R Q) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := R⁰) Q
    (toMinimalPrimeFractions R Q).toRingHom
  intro r hr
  have hrnil : r ∈ (⊥ : Ideal R).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    apply Ideal.mem_sInf.mpr
    intro p hp
    let : Ideal.IsPrime p := hp.isPrime
    have hcomp := congrFun hr (⟨p, hp⟩ : minimalPrimes R)
    change toMinimalPrimeFraction R Q p hp (algebraMap R Q r) = 0 at hcomp
    rw [toMinimalPrimeFraction_algebraMap,
      IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p))] at hcomp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))
    simpa only [Ideal.Quotient.algebraMap_eq, map_zero] using hcomp
  have hrzero : r = 0 := by
    apply isNilpotent_iff_eq_zero.mp
    obtain ⟨n, hn⟩ := hrnil
    exact ⟨n, Ideal.mem_bot.mp hn⟩
  simp only [hrzero, map_zero]

/-- The actual normalization maps to the product of the normalizations of
the actual minimal-prime quotients. -/
def toMinimalPrimeNormalizations :
    integralClosure R Q →ₐ[R]
      ∀ p : minimalPrimes R, integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val)) :=
  AlgHom.pi fun p ↦ toMinimalPrimeNormalization R Q p.val p.property

/-- The normalization-to-components map is injective for a reduced base. -/
theorem toMinimalPrimeNormalizations_injective [IsReduced R] :
    Function.Injective (toMinimalPrimeNormalizations R Q) := by
  intro x y h
  apply Subtype.ext
  apply toMinimalPrimeFractions_injective R Q
  funext p
  exact congrArg Subtype.val (congrFun h p)

end Components

section ReducedComplete

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

private theorem finite_primeQuotient_normalization (p : Ideal R) (hp : p.IsPrime) :
    Module.Finite R (integralClosure (R ⧸ p) (FractionRing (R ⧸ p))) := by
  let : p.IsPrime := hp
  let : IsNoetherianRing (R ⧸ p) := isNoetherianRing_of_surjective R (R ⧸ p)
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (R ⧸ p) := Ring.krullDimLE_iff.mpr
    ((ringKrullDim_quotient_le p).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R)))
  let : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ p)) (R ⧸ p) := by
    have h := IsAdicComplete.map_algebraMap_of_finite R (IsLocalRing.maximalIdeal R) (R ⧸ p)
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap R (R ⧸ p)) Ideal.Quotient.mk_surjective] at h
  let : Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p))) :=
    finite_of_complete_local_dimLE_one (R ⧸ p) (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p))
  exact Module.Finite.trans (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))

variable (Q : Type*) [CommRing Q] [Algebra R Q] [IsFractionRing R Q]

/-- The literal normalization of a reduced complete Noetherian local ring
of dimension at most one in its total quotient ring is finite. -/
theorem finite_of_complete_local_reduced_dimLE_one [IsReduced R] :
    Module.Finite R (integralClosure R Q) := by
  classical
  let : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing (R := R)).fintype
  let : ∀ p : minimalPrimes R,
      Module.Finite R (integralClosure (R ⧸ p.val) (FractionRing (R ⧸ p.val))) :=
    fun p ↦ finite_primeQuotient_normalization R p.val p.property.isPrime
  exact Module.Finite.of_injective (toMinimalPrimeNormalizations R Q).toLinearMap
    (toMinimalPrimeNormalizations_injective R Q)

/-- The normalization quotient of a reduced complete local curve has
finite length over the original coefficient ring. The ambient fraction
ring is the original total quotient ring. -/
theorem quotient_isFiniteLength_of_complete_local_reduced_dimLE_one [IsReduced R] :
    IsFiniteLength R
      (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap R (integralClosure R Q))) := by
  let : Module.Finite R (integralClosure R Q) := finite_of_complete_local_reduced_dimLE_one R Q
  exact quotient_isFiniteLength R Q

end ReducedComplete

end integralClosure
