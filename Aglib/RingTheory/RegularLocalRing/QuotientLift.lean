/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Localization
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Lifting regular locality through a regular principal quotient

Minimal generators of the quotient maximal ideal lift to generators together
with the original equation. The nonzerodivisor dimension inequality then
gives regularity of the original Noetherian local ring. No hypothesis that
the equation lies outside the square of the maximal ideal is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing
open scoped nonZeroDivisors

universe u

namespace IsLocalRing

/-- A principal quotient lowers the maximal-ideal generator number by at most one. -/
theorem spanFinrank_maximalIdeal_le_quotient_add_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
  classical
  let q := Ideal.Quotient.mk (Ideal.span {x})
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  let m := maximalIdeal (R ⧸ Ideal.span {x})
  let t := g '' m.generators
  have hfg : Submodule.FG m := m.fg_of_isNoetherianRing
  have ht : t.Finite := hfg.finite_generators.image g
  have himage : q '' t = m.generators := by
    rw [show t = g '' m.generators from rfl, ← Set.image_comp]
    simp only [q, g, Function.comp_surjInv, Set.image_id]
  have hmap : (Ideal.span t).map q = m := by
    rw [Ideal.map_span, himage]
    exact Submodule.span_generators m
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have he := congrArg (Ideal.comap q) hmap
  have hker : Ideal.comap q ⊥ = Ideal.span {x} := Ideal.mk_ker
  rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective, hker,
    show m.comap q = maximalIdeal R from maximalIdeal_comap q] at he
  have hgen : Ideal.span (insert x t) = maximalIdeal R := by
    rw [Ideal.span_insert, sup_comm]
    exact he
  rw [← hgen]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (ht.insert x)).trans
  apply (Set.ncard_insert_le x t).trans
  apply Nat.add_le_add_right
  exact (Set.ncard_image_le hfg.finite_generators).trans_eq hfg.generators_ncard

end IsLocalRing

namespace IsRegularLocalRing

/-- A Noetherian local ring with regular quotient by a nonzerodivisor is regular local. -/
@[stacks 00NU]
theorem of_quotient_span_singleton
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : IsSMulRegular R x) [IsRegularLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing R := by
  have hreg : x ∈ R⁰ := mem_nonZeroDivisors_iff_left.mpr fun r hr ↦
    hx (by simpa only [smul_eq_mul, mul_zero] using hr)
  apply of_spanFinrank_maximalIdeal_le
  have hgen := IsLocalRing.spanFinrank_maximalIdeal_le_quotient_add_one R x
  have hbound : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    rw [← spanFinrank_maximalIdeal]
    exact_mod_cast hgen
  exact hbound.trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg)

/-- At a prime containing a regular equation, regularity of its global quotient
gives regularity of the original prime localization. -/
theorem atPrime_of_quotient_span_singleton
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (x : R) (hx : IsSMulRegular R x)
    [IsRegularRing (R ⧸ Ideal.span {x})]
    (p : Ideal R) [p.IsPrime] (hxp : x ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let J := Ideal.span {x}
  let K := J.map (algebraMap R S)
  have hK : K = Ideal.span {algebraMap R S x} := by simp [K, J, Ideal.map_span]
  have hproper : K ≠ ⊤ := by
    apply ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
    rw [hK, Ideal.span_singleton_le_iff_mem, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hxp
  let : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (S ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  let : IsRegularRing (S ⧸ K) :=
    IsRegularRing.regular_localization (R ⧸ J) (S ⧸ K)
      (Algebra.algebraMapSubmonoid (R ⧸ J) p.primeCompl)
  have hquot : IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S x}) := by
    rw [← hK]
    exact of_isRegularRing_of_isLocalRing _
  let := hquot
  have hx0 : x ∈ R⁰ := mem_nonZeroDivisors_iff_left.mpr fun r hr ↦
    hx (by simpa only [smul_eq_mul, mul_zero] using hr)
  have hxS : algebraMap R S x ∈ S⁰ :=
    IsLocalization.nonZeroDivisors_le_comap p.primeCompl S hx0
  apply of_quotient_span_singleton S (algebraMap R S x)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro r hr
  exact (mem_nonZeroDivisors_iff_left.mp hxS) r (by simpa only [smul_eq_mul] using hr)

end IsRegularLocalRing
