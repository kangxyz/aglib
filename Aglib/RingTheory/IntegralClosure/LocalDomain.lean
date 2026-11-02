/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.TotalFractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Domainhood of reduced Noetherian integrally closed local rings

The original idempotent argument is extracted from
`AdicCompletion/NormalSurface`. The supplied total quotient ring is preserved;
its Artinian decomposition and integral closedness force a single field factor.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace IsIntegrallyClosed

private theorem idempotent_eq_zero_or_one_of_local
    (C : Type u) [CommRing C] [IsLocalRing C] (e : C) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  rcases isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (h.mul_left_cancel (by simpa only [mul_one] using he))
  · apply Or.inl
    apply h.mul_left_cancel
    simp only [sub_mul, one_mul, he, sub_self, mul_zero]

private theorem idempotent_isIntegral
    (C F : Type u) [CommRing C] [CommRing F] [Algebra C F]
    (e : F) (he : e * e = e) : IsIntegral C e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X,
    Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    pow_two, he, sub_self]

/-- A local integrally closed ring whose actual total quotient ring is
reduced and Artinian is a domain. -/
theorem isDomain_of_artinian_total_fraction_ring
    (C F : Type u) [CommRing C] [IsLocalRing C] [IsIntegrallyClosed C]
    [CommRing F] [Algebra C F] [IsFractionRing C F]
    [IsReduced F] [IsArtinianRing F] : IsDomain C := by
  classical
  let : Nontrivial F := ⟨⟨0, 1, fun h => zero_ne_one
    ((IsFractionRing.injective C F) (by simpa only [_root_.map_zero, map_one] using h))⟩⟩
  let E := IsArtinianRing.equivPi F
  have hsub : Subsingleton (MaximalSpectrum F) := by
    constructor
    intro i j
    by_contra hij
    let v : ∀ k : MaximalSpectrum F, F ⧸ k.asIdeal := fun k => if k = i then 1 else 0
    let e : F := E.symm v
    have he : e * e = e := by
      apply E.injective
      change E (E.symm v * E.symm v) = E (E.symm v)
      rw [map_mul, E.apply_symm_apply]
      funext k
      by_cases hk : k = i <;> simp [v, hk]
    obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff F).mp
      (inferInstance : IsIntegrallyClosed C) (idempotent_isIntegral C F e he)
    have hcIdem : c * c = c := by
      apply IsFractionRing.injective C F
      rw [map_mul, hc, he]
    rcases idempotent_eq_zero_or_one_of_local C c hcIdem with hc0 | hc1
    · have he0 : e = 0 := by rw [← hc, hc0, _root_.map_zero]
      have hv0 := congrFun (congrArg E he0) i
      simp [e, v] at hv0
    · have he1 : e = 1 := by rw [← hc, hc1, map_one]
      have hv1 := congrFun (congrArg E he1) j
      have hji : j ≠ i := Ne.symm hij
      simp [e, v, hji] at hv1
  let i : MaximalSpectrum F := Classical.choice inferInstance
  let : Unique (MaximalSpectrum F) := ⟨⟨i⟩, fun j => hsub.elim j i⟩
  let e : F ≃+* F ⧸ i.asIdeal := E.toRingEquiv.trans (RingEquiv.piUnique _)
  let : Field (F ⧸ i.asIdeal) := Ideal.Quotient.field _
  let : IsDomain F := Function.Injective.isDomain e e.injective
  exact Function.Injective.isDomain (algebraMap C F) (IsFractionRing.injective C F)

/-- A reduced Noetherian integrally closed local ring is a domain.
Artinianity is proved for its genuine total quotient ring, not assumed for
an unrelated generic fibre. -/
theorem isDomain_of_isLocalRing_of_isReduced
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsReduced C]
    [IsLocalRing C] [IsIntegrallyClosed C] : IsDomain C := by
  let : IsArtinianRing (FractionRing C) := FractionRing.isArtinianRing_of_isReduced C
  exact isDomain_of_artinian_total_fraction_ring C (FractionRing C)

end IsIntegrallyClosed
