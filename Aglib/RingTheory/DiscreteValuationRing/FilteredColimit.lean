/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Marked DVRs in actual filtered colimits

A filtered colimit of DVRs with the same natural uniformizer, and an
actual compatible point in a field, is again a DVR. Regularity is proved
by equality at a later stage. The unit-power factorizations and kernel
equation are mapped from actual representatives. The result retains the
original colimit carrier, cocone maps, and field point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace CommRingCat

universe u v

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc

private theorem isLocalRing_of_isColimit [∀ i, IsLocalRing (F.obj i)] :
    IsLocalRing c.pt := by
  let : Nontrivial c.pt := CommRingCat.FilteredColimits.nontrivial hc
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with hy | hy
  · exact Or.inl (hy.map (c.ι.app i).hom)
  · exact Or.inr (by simpa only [map_sub, map_one] using hy.map (c.ι.app i).hom)

private theorem regular_natCast_of_isColimit [∀ i, IsDomain (F.obj i)]
    (p : ℕ) (hp : ∀ i, (p : F.obj i) ≠ 0) : IsSMulRegular c.pt (p : c.pt) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  have heq : (c.ι.app i).hom ((p : F.obj i) * y) = (c.ι.app i).hom 0 := by
    simpa only [map_mul, map_natCast, map_zero, smul_eq_mul] using hx
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat) hc)
      ((p : F.obj i) * y) (0 : F.obj i)).mp heq
  change (F.map f).hom ((p : F.obj i) * y) = (F.map f).hom 0 at hf
  have hf' : (p : F.obj j) * (F.map f).hom y = 0 := by
    simpa only [map_mul, map_natCast, map_zero] using hf
  have hy : (F.map f).hom y = 0 := (mul_eq_zero.mp hf').resolve_left (hp j)
  have hw := ConcreteCategory.congr_hom (c.w f) y
  change (c.ι.app j).hom ((F.map f).hom y) = (c.ι.app i).hom y at hw
  rw [← hw, hy, map_zero]

private theorem factorization_of_isColimit
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i)) {x : c.pt} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : c.ptˣ), x = u * (p : c.pt) ^ n := by
  obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  have hy : y ≠ 0 := by
    intro h
    apply hx
    rw [h, map_zero]
  obtain ⟨n, u, hy⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (hp i)
  obtain ⟨v, hv⟩ := u.isUnit.map (c.ι.app i).hom
  refine ⟨n, v, ?_⟩
  rw [hy, map_mul, map_pow, map_natCast, ← hv]

/-- The actual colimit is a domain; no injectivity of transition maps is
assumed. The common natural uniformizer controls every representative. -/
theorem isDomain_of_isColimit_of_uniformizer
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i)) : IsDomain c.pt := by
  let : Nontrivial c.pt := CommRingCat.FilteredColimits.nontrivial hc
  have hreg := regular_natCast_of_isColimit F c hc p (fun i ↦ (hp i).ne_zero)
  have hpow (n : ℕ) : (p : c.pt) ^ n ≠ 0 := by
    intro h
    have hone : (1 : c.pt) = 0 := (IsSMulRegular.pow n hreg).right_eq_zero_of_smul
      (by simpa only [smul_eq_mul, mul_one] using h)
    exact one_ne_zero hone
  let : NoZeroDivisors c.pt := ⟨by
    intro x y hxy
    by_contra! h
    obtain ⟨n, u, rfl⟩ := factorization_of_isColimit F c hc p hp h.1
    obtain ⟨m, v, rfl⟩ := factorization_of_isColimit F c hc p hp h.2
    have he : (u : c.pt) * (p : c.pt) ^ n * ((v : c.pt) * (p : c.pt) ^ m) =
        (u * v : c.ptˣ) * (p : c.pt) ^ (n + m) := by
      simp only [Units.val_mul, pow_add]
      ac_rfl
    rw [he] at hxy
    exact hpow (n + m) ((u * v).isUnit.mul_right_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain c.pt

private theorem ker_eq_span_of_isColimit
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i))
    {K : Type v} [Field K] (g : c.pt →+* K)
    (hg : ∀ i, RingHom.ker (g.comp (c.ι.app i).hom) = maximalIdeal (F.obj i)) :
    RingHom.ker g = Ideal.span {(p : c.pt)} := by
  have hpker : (p : c.pt) ∈ RingHom.ker g := by
    let i : J := Classical.choice (IsFiltered.nonempty (C := J))
    have hi : (p : F.obj i) ∈ RingHom.ker (g.comp (c.ι.app i).hom) := by
      rw [hg i, (hp i).maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    change g ((c.ι.app i).hom (p : F.obj i)) = 0 at hi
    change g (p : c.pt) = 0
    simpa only [map_natCast] using hi
  apply le_antisymm
  · intro x hx
    obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    have hy : y ∈ RingHom.ker (g.comp (c.ι.app i).hom) := hx
    rw [hg i, (hp i).maximalIdeal_eq, Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(c.ι.app i).hom z, ?_⟩
    simpa only [map_mul, map_natCast] using congrArg (c.ι.app i).hom hz
  · exact (Ideal.span_singleton_le_iff_mem (RingHom.ker g)).mpr hpker

private theorem ker_eq_maximalIdeal_of_isColimit
    [∀ i, IsLocalRing (F.obj i)] {K : Type v} [Field K] (g : c.pt →+* K)
    (hg : ∀ i, RingHom.ker (g.comp (c.ι.app i).hom) = maximalIdeal (F.obj i)) :
    let _ : IsLocalRing c.pt := isLocalRing_of_isColimit F c hc
    RingHom.ker g = maximalIdeal c.pt := by
  let : IsLocalRing c.pt := isLocalRing_of_isColimit F c hc
  ext x
  constructor
  · intro hx hu
    exact (hu.map g).ne_zero hx
  · intro hx
    obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    have hy : y ∈ maximalIdeal (F.obj i) := fun hu ↦ hx (hu.map (c.ι.app i).hom)
    exact (hg i).symm.le hy

/-- The actual filtered colimit of marked DVRs is a DVR. The field point
need not be surjective, and the transition maps need not be supplied as
injective or flat. -/
theorem isDiscreteValuationRing_of_isColimit_of_uniformizer
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i))
    {K : Type v} [Field K] (g : c.pt →+* K)
    (hg : ∀ i, RingHom.ker (g.comp (c.ι.app i).hom) = maximalIdeal (F.obj i)) :
    let _ : IsDomain c.pt := isDomain_of_isColimit_of_uniformizer F c hc p hp
    IsDiscreteValuationRing c.pt := by
  let : IsDomain c.pt := isDomain_of_isColimit_of_uniformizer F c hc p hp
  let : IsLocalRing c.pt := isLocalRing_of_isColimit F c hc
  have hm : maximalIdeal c.pt = Ideal.span {(p : c.pt)} :=
    (ker_eq_maximalIdeal_of_isColimit F c hc g hg).symm.trans
      (ker_eq_span_of_isColimit F c hc p hp g hg)
  have hreg := regular_natCast_of_isColimit F c hc p (fun i ↦ (hp i).ne_zero)
  have hp0 : (p : c.pt) ≠ 0 := by
    intro h
    have hone : (1 : c.pt) = 0 :=
      hreg.right_eq_zero_of_smul (by simp only [h, zero_smul])
    exact one_ne_zero hone
  have hirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : c.pt) hp0 hm
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨(p : c.pt), hirr, ?_⟩
  intro x hx
  obtain ⟨n, u, rfl⟩ := factorization_of_isColimit F c hc p hp hx
  exact ⟨n, ⟨u, by simp [mul_comm]⟩⟩

/-- The original field point retains the actual maximal ideal as kernel
after passage to the colimit DVR. -/
theorem ker_point_of_isColimit_of_uniformizer
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i))
    {K : Type v} [Field K] (g : c.pt →+* K)
    (hg : ∀ i, RingHom.ker (g.comp (c.ι.app i).hom) = maximalIdeal (F.obj i)) :
    let _ : IsDomain c.pt := isDomain_of_isColimit_of_uniformizer F c hc p hp
    let _ : IsDiscreteValuationRing c.pt :=
      isDiscreteValuationRing_of_isColimit_of_uniformizer F c hc p hp g hg
    RingHom.ker g = maximalIdeal c.pt :=
  ker_eq_maximalIdeal_of_isColimit F c hc g hg

/-- The same natural coefficient is a uniformizer in the actual colimit. -/
theorem irreducible_natCast_of_isColimit
    [∀ i, IsDomain (F.obj i)] [∀ i, IsDiscreteValuationRing (F.obj i)]
    (p : ℕ) (hp : ∀ i, Irreducible (p : F.obj i))
    {K : Type v} [Field K] (g : c.pt →+* K)
    (hg : ∀ i, RingHom.ker (g.comp (c.ι.app i).hom) = maximalIdeal (F.obj i)) :
    Irreducible (p : c.pt) := by
  let : IsDomain c.pt := isDomain_of_isColimit_of_uniformizer F c hc p hp
  let : IsDiscreteValuationRing c.pt :=
    isDiscreteValuationRing_of_isColimit_of_uniformizer F c hc p hp g hg
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  exact (ker_point_of_isColimit_of_uniformizer F c hc p hp g hg).symm.trans
    (ker_eq_span_of_isColimit F c hc p hp g hg)

end CommRingCat
