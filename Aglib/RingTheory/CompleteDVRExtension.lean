/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteModule
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Henselian

/-!
# Finite extensions of complete discrete valuation rings

The locality argument uses actual idempotent lifting for `X ^ 2 - X` over the
extended ideal, followed by the Artinianity of the closed fibre. No locality
or compatibility of the integral closure is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace IsDiscreteValuationRing.CompleteExtension

/-- An Artinian commutative ring with no nontrivial idempotents is local. -/
theorem isLocalRing_of_artinian_of_idempotents
    (A : Type*) [CommRing A] [Nontrivial A] [IsArtinianRing A]
    (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing A := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨n, b, hb⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  have hab : a ^ n * (a * b) = a ^ n := by
    simpa only [smul_eq_mul, mul_one, pow_succ, mul_assoc] using hb
  have habpow (k : ℕ) : a ^ n * (a * b) ^ k = a ^ n := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hab]
  have he : IsIdempotentElem ((a * b) ^ n) := by
    change (a * b) ^ n * (a * b) ^ n = (a * b) ^ n
    calc
      _ = (a ^ n * (a * b) ^ n) * b ^ n := by ring
      _ = a ^ n * b ^ n := by rw [habpow]
      _ = (a * b) ^ n := (mul_pow ..).symm
  rcases h _ he with hz | ho
  · right
    have ha : a ^ n = 0 := by simpa only [hz, mul_zero] using (habpow n).symm
    exact (show IsNilpotent a from ⟨n, ha⟩).isUnit_one_sub
  · left
    by_cases hn : n = 0
    · subst n
      exact isUnit_iff_exists_inv.mpr ⟨b, by simpa using hab⟩
    · exact ((Commute.all a b).isUnit_mul_iff.mp
        ((isUnit_pow_iff hn).mp (ho ▸ isUnit_one))).1

/-- Idempotents in a quotient lift along a henselian ideal. -/
theorem exists_idempotent_lift (A : Type*) [CommRing A] [Nontrivial A] (I : Ideal A)
    [HenselianRing A I] (e : A ⧸ I) (he : IsIdempotentElem e) :
    ∃ x : A, IsIdempotentElem x ∧ Ideal.Quotient.mk I x = e := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
  let f : A[X] := X ^ 2 - X
  have hf : f.Monic := monic_X_pow_sub (by simp)
  have hroot : f.eval a ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [f, pow_two, he.eq]
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) := by
    have hsq : (2 * Ideal.Quotient.mk I a - 1) *
        (2 * Ideal.Quotient.mk I a - 1) = 1 := by
      calc
        _ = 4 * (Ideal.Quotient.mk I a * Ideal.Quotient.mk I a -
          Ideal.Quotient.mk I a) + 1 := by ring
        _ = 1 := by rw [he.eq]; ring
    simpa [f, derivative_X_pow, ← two_mul, map_ofNat] using (isUnit_iff_exists_inv.mpr ⟨_, hsq⟩)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian f hf a hroot hderiv
  refine ⟨x, ?_, ?_⟩
  · simpa [IsIdempotentElem, f, IsRoot, pow_two, sub_eq_zero] using hx
  · rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hxa

/-- A henselian domain with Artinian closed fibre is a local ring. -/
theorem isLocalRing_of_henselian_of_artinian_quotient
    (A : Type*) [CommRing A] [IsDomain A] (I : Ideal A)
    [HenselianRing A I] [Nontrivial (A ⧸ I)] [IsArtinianRing (A ⧸ I)] :
    IsLocalRing A := by
  have : IsLocalRing (A ⧸ I) := isLocalRing_of_artinian_of_idempotents _ (by
    intro e he
    obtain ⟨x, hx, rfl⟩ := exists_idempotent_lift A I e he
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hx with rfl | rfl <;> simp)
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := A) (I := I))
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk I a) with h | h
  · exact Or.inl (IsUnit.of_map (Ideal.Quotient.mk I) _ h)
  · exact Or.inr (IsUnit.of_map (Ideal.Quotient.mk I) _ (by simpa using h))


/-- A finite domain over a complete Noetherian local ring is local. -/
theorem isLocalRing_of_finite
    (R A : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Finite R A] : IsLocalRing A := by
  let I := (maximalIdeal R).map (algebraMap R A)
  have : IsAdicComplete I A := IsAdicComplete.map_algebraMap_of_finite R _ A
  have hI : I ≠ ⊤ := by
    intro h
    have hj := IsAdicComplete.le_jacobson_bot I
    rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hj
    exact bot_ne_top hj
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : Algebra (ResidueField R) (A ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (ResidueField R) (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite R (A ⧸ I) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom R A (A ⧸ I)).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (ResidueField R) (A ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite (ResidueField R) _
  exact isLocalRing_of_henselian_of_artinian_quotient A I


/-- Completeness for a positive ideal power implies completeness for the ideal. -/
theorem isAdicComplete_of_pow (A : Type*) [CommRing A] (I : Ideal A)
    (n : ℕ) (hn : 0 < n) [IsAdicComplete (I ^ n) A] : IsAdicComplete I A where
  haus' x hx := IsHausdorff.haus' (I := I ^ n) x (fun k => by
    simpa only [← pow_mul] using hx (n * k))
  prec' f hf := by
    obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := I ^ n) (fun k => f (n * k)) (by
      intro i j hij
      simpa only [← pow_mul] using hf (Nat.mul_le_mul_left n hij))
    refine ⟨x, fun k => ?_⟩
    have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    exact (hf hk).trans (SModEq.mono (by
      simpa only [← pow_mul, Ideal.smul_eq_mul, Ideal.mul_top] using
        (Ideal.pow_le_pow_right hk : I ^ (n * k) ≤ I ^ k)) (hx k))


/-- A local injective map of DVRs sends a uniformizer to a positive unit times power. -/
-- Keep the source DVR condition in this local-DVR ramification API.
@[nolint unusedArguments]
theorem exists_positive_ramification
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Injective f)
    {π : R} (hπ : Irreducible π) {ϖ : S} (hϖ : Irreducible ϖ) :
    ∃ (e : ℕ) (_ : 0 < e) (u : Sˣ), f π = u * ϖ ^ e := by
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff f hf).mpr hπ.ne_zero) hϖ
  refine ⟨e, ?_, u, he⟩
  apply Nat.pos_of_ne_zero
  intro hz
  apply hπ.not_isUnit
  apply IsUnit.of_map f π
  rw [he, hz, pow_zero, mul_one]
  exact u.isUnit

/-- A field embedding restricts to a local map on the actual integral closures. -/
theorem mapIntegralClosure_isLocalHom
    {R E L : Type*} [CommRing R] [Field E] [Field L] [Algebra R E] [Algebra R L]
    (f : E →ₐ[R] L) : IsLocalHom f.mapIntegralClosure.toRingHom := by
  have hi : f.mapIntegralClosure.toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap R (integralClosure R E))
    have hc : f.mapIntegralClosure.toRingHom.comp (algebraMap R (integralClosure R E)) =
        algebraMap R (integralClosure R L) := by
      exact RingHom.ext fun x => f.mapIntegralClosure.commutes x
    rw [hc]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  apply hi.isLocalHom
  intro x y h
  apply Subtype.ext
  apply f.injective
  exact congrArg (fun z : integralClosure R L => (z : L)) h

section IntegralClosure

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K

/-- The actual integral closure in a finite separable fraction-field extension is local. -/
theorem integralClosure_isLocalRing : IsLocalRing (integralClosure R L) := by
  have : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  exact isLocalRing_of_finite R (integralClosure R L)

omit [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The algebra map into the actual integral closure is injective. -/
theorem integralClosure_algebraMap_injective :
    Function.Injective (algebraMap R (integralClosure R L)) := by
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  intro x y h
  apply hinj
  exact congrArg (algebraMap (integralClosure R L) L) h

/-- The actual integral closure is a DVR, not merely a semilocal Dedekind domain. -/
theorem integralClosure_isDiscreteValuationRing :
    IsDiscreteValuationRing (integralClosure R L) := by
  have : IsLocalRing (integralClosure R L) := integralClosure_isLocalRing R K L
  have : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  have hnf : ¬ IsField (integralClosure R L) := by
    intro h
    exact IsDiscreteValuationRing.not_isField R
      (isField_of_isIntegral_of_isField (integralClosure_algebraMap_injective R K L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 1 3).mpr
    (show IsDedekindDomain (integralClosure R L) from inferInstance)


omit [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The literal algebra map into the integral closure is a local homomorphism. -/
theorem integralClosure_isLocalHom : IsLocalHom (algebraMap R (integralClosure R L)) :=
  (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
    (integralClosure_algebraMap_injective R K L)

/-- The actual integral closure is complete for its own maximal ideal. -/
theorem integralClosure_isAdicComplete :
    let _ := integralClosure_isLocalRing R K L
    IsAdicComplete (maximalIdeal (integralClosure R L)) (integralClosure R L) := by
  let _ := integralClosure_isDiscreteValuationRing R K L
  have : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  have : IsLocalHom (algebraMap R (integralClosure R L)) :=
    integralClosure_isLocalHom R K L
  let I := (maximalIdeal R).map (algebraMap R (integralClosure R L))
  have hcomplete : IsAdicComplete I (integralClosure R L) :=
    IsAdicComplete.map_algebraMap_of_finite R _ _
  have hI : I ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_a_field R
      ((Ideal.map_eq_bot_iff_of_injective
        (integralClosure_algebraMap_injective R K L)).mp h)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal (integralClosure R L)
    (inferInstance : (maximalIdeal (integralClosure R L)).IsPrincipal) I hI
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have ht := IsLocalRing.map_maximalIdeal_lt_top (algebraMap R (integralClosure R L))
    have : I = ⊤ := by simpa only [hz, pow_zero, Ideal.one_eq_top] using hn
    exact ne_of_lt ht this
  have : IsAdicComplete (maximalIdeal (integralClosure R L) ^ n) (integralClosure R L) :=
    hn ▸ hcomplete
  exact isAdicComplete_of_pow _ _ n hnpos


/-- The actual residue-field extension of the integral closure is finite. -/
theorem integralClosure_residue_finite :
    let _ := integralClosure_isLocalRing R K L
    let _ := integralClosure_isLocalHom R K L
    Module.Finite (ResidueField R) (ResidueField (integralClosure R L)) := by
  let _ := integralClosure_isLocalRing R K L
  let _ := integralClosure_isLocalHom R K L
  have : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  exact IsLocalRing.ResidueField.finite_of_module_finite

/-- Completeness supplies Hensel lifting on the actual integral closure. -/
theorem integralClosure_henselianLocalRing : HenselianLocalRing (integralClosure R L) := by
  let _ := integralClosure_isLocalRing R K L
  let _ := integralClosure_isAdicComplete R K L
  exact { is_henselian := fun p hp a ha hd =>
    HenselianRing.is_henselian p hp a ha (hd.map _) }

/-- The literal base algebra map has positive ramification at every chosen uniformizer. -/
theorem integralClosure_exists_positive_ramification
    {π : R} (hπ : Irreducible π) {ϖ : integralClosure R L} (hϖ : Irreducible ϖ) :
    ∃ (e : ℕ) (_ : 0 < e) (u : (integralClosure R L)ˣ),
      algebraMap R (integralClosure R L) π = u * ϖ ^ e := by
  let _ := integralClosure_isDiscreteValuationRing R K L
  let _ := integralClosure_isLocalHom R K L
  exact exists_positive_ramification _ (integralClosure_algebraMap_injective R K L) hπ hϖ

end IntegralClosure

end IsDiscreteValuationRing.CompleteExtension
