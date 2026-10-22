/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# The actual denominator ideal of finite fractional coordinates

The denominator ideal is the native submodule colon of the integral fractional
ideal by the specified fractional ideal. For a finite family containing the
original coordinate one, a GCD domain supplies an actual nonzero generator.
The proof uses one common denominator and the gcd of its actual numerators.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u v w

namespace FractionalIdeal

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The integral elements that multiply the original fractional ideal into the
original integral fractional ideal. This also has its usual meaning at zero. -/
def denominatorIdeal (L : FractionalIdeal R⁰ K) : Ideal R :=
  ((1 : FractionalIdeal R⁰ K) : Submodule R K).colon (L : Set K)

omit [IsDomain R] [IsFractionRing R K] in
/-- Membership retains the original coefficient map and multiplication in K. -/
theorem mem_denominatorIdeal (L : FractionalIdeal R⁰ K) (r : R) :
    r ∈ denominatorIdeal L ↔
      ∀ x ∈ L, algebraMap R K r * x ∈ (1 : FractionalIdeal R⁰ K) := by
  rw [denominatorIdeal, Submodule.mem_colon]
  constructor
  · intro h x hx
    apply (mem_coe (I := (1 : FractionalIdeal R⁰ K))).mp
    simpa only [Algebra.smul_def] using h x hx
  · intro h x hx
    simpa only [Algebra.smul_def] using
      (mem_coe (I := (1 : FractionalIdeal R⁰ K))).mpr (h x hx)

omit [IsDomain R] in
/-- For a finite span, it suffices to test the originally supplied generators. -/
theorem mem_denominatorIdeal_spanFinset {ι : Type w} (s : Finset ι) (f : ι → K)
    (r : R) :
    r ∈ denominatorIdeal (spanFinset R s f) ↔
      ∀ i ∈ s, algebraMap R K r * f i ∈ (1 : FractionalIdeal R⁰ K) := by
  change r ∈ ((1 : FractionalIdeal R⁰ K) : Submodule R K).colon
    ((Submodule.span R (f '' (s : Set ι))) : Set K) ↔ _
  rw [Submodule.colon_span, Submodule.mem_colon]
  constructor
  · intro h i hi
    simpa only [Algebra.smul_def, mem_coe] using h (f i) ⟨i, hi, rfl⟩
  · intro h y hy
    obtain ⟨i, hi, rfl⟩ := hy
    simpa only [Algebra.smul_def, mem_coe] using h i hi

omit [IsDomain R] in
/-- An actual common denominator turns denominator membership into original
ring divisibility. No field section or chosen isomorphism is substituted. -/
theorem mem_denominatorIdeal_spanFinset_iff_dvd {ι : Type w}
    (s : Finset ι) (f : ι → K) (d : R) (hd : d ≠ 0) (a : ι → R)
    (ha : ∀ i ∈ s, algebraMap R K (a i) = algebraMap R K d * f i) (r : R) :
    r ∈ denominatorIdeal (spanFinset R s f) ↔ ∀ i ∈ s, d ∣ r * a i := by
  rw [mem_denominatorIdeal_spanFinset]
  have hdK : algebraMap R K d ≠ 0 :=
    fun h => hd ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  constructor
  · intro h i hi
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (h i hi)
    refine ⟨b, ?_⟩
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ha i hi, hb]
    ring
  · intro h i hi
    obtain ⟨b, hb⟩ := h i hi
    apply (mem_one_iff R⁰).mpr
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ hdK
    calc
      algebraMap R K d * algebraMap R K b =
          algebraMap R K r * algebraMap R K (a i) := by
        simpa only [map_mul] using (congrArg (algebraMap R K) hb).symm
      _ = algebraMap R K d * (algebraMap R K r * f i) := by
        rw [ha i hi]
        ring

/-- The canonical linear numerator map for an actual denominator and an actual
element of the original fractional ideal. -/
def numeratorLinearMap (L : FractionalIdeal R⁰ K) (x : L) :
    denominatorIdeal L →ₗ[R] R where
  toFun d := ((mem_one_iff R⁰).mp
    ((mem_denominatorIdeal L d).mp d.property x x.property)).choose
  map_add' d e := by
    apply IsFractionRing.injective R K
    have hd := ((mem_one_iff R⁰).mp
      ((mem_denominatorIdeal L d).mp d.property x x.property)).choose_spec
    have he := ((mem_one_iff R⁰).mp
      ((mem_denominatorIdeal L e).mp e.property x x.property)).choose_spec
    have hde := ((mem_one_iff R⁰).mp
      ((mem_denominatorIdeal L (d + e)).mp (d + e).property x x.property)).choose_spec
    simpa only [Submodule.coe_add, map_add, add_mul, hd, he] using hde
  map_smul' r d := by
    apply IsFractionRing.injective R K
    have hd := ((mem_one_iff R⁰).mp
      ((mem_denominatorIdeal L d).mp d.property x x.property)).choose_spec
    have hrd := ((mem_one_iff R⁰).mp
      ((mem_denominatorIdeal L (r • d)).mp (r • d).property x x.property)).choose_spec
    simpa only [Submodule.coe_smul, smul_eq_mul, map_mul, mul_assoc, RingHom.id_apply, hd] using hrd

omit [IsDomain R] in
/-- The linear numerator is evaluated through the original ring-to-field map. -/
theorem map_numeratorLinearMap (L : FractionalIdeal R⁰ K) (x : L)
    (d : denominatorIdeal L) :
    algebraMap R K (numeratorLinearMap L x d) = algebraMap R K d * (x : K) :=
  ((mem_one_iff R⁰).mp
    ((mem_denominatorIdeal L d).mp d.property x x.property)).choose_spec

/-- In a GCD domain, the denominator ideal of finitely many actual fractional
coordinates including one has an actual nonzero generator. -/
theorem exists_denominatorIdeal_spanFinset_generator [IsGCDMonoid R]
    {ι : Type w} (s : Finset ι) (f : ι → K) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (hf : f i₀ = 1) :
    ∃ c : R, c ≠ 0 ∧ denominatorIdeal (spanFinset R s f) = Ideal.span {c} := by
  classical
  let : NormalizedGCDMonoid R := Classical.arbitrary _
  let d : nonZeroDivisors R := IsLocalization.commonDenom R⁰ s f
  let a (i : ι) : R := if hi : i ∈ s then
    IsLocalization.integerMultiple R⁰ s f ⟨i, hi⟩ else 0
  have hd : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have ha (i : ι) (hi : i ∈ s) :
      algebraMap R K (a i) = algebraMap R K (d : R) * f i := by
    dsimp only [a]
    rw [dite_eq_left hi]
    simpa only [d, Submonoid.smul_def, Algebra.smul_def] using
      IsLocalization.map_integerMultiple R⁰ s f ⟨i, hi⟩
  have ha₀ : a i₀ = (d : R) := by
    apply IsFractionRing.injective R K
    rw [ha i₀ hi₀, hf, mul_one]
  let g : R := s.gcd a
  have hgd : g ∣ (d : R) := by
    simpa only [g, ha₀] using (Finset.gcd_dvd (f := a) hi₀)
  have hg : g ≠ 0 := by
    intro hzero
    exact hd (zero_dvd_iff.mp (hzero ▸ hgd))
  obtain ⟨c, hc⟩ := hgd
  have hc₀ : c ≠ 0 := by
    intro hzero
    exact hd (by rw [hc, hzero, mul_zero])
  refine ⟨c, hc₀, ?_⟩
  ext r
  rw [mem_denominatorIdeal_spanFinset_iff_dvd s f (d : R) hd a ha,
    Ideal.mem_span_singleton]
  have hmul : (d : R) ∣ r * g ↔ ∀ i ∈ s, (d : R) ∣ r * a i := by
    rw [← (Finset.gcd_mul_left' s a r).dvd_iff_dvd_right, Finset.dvd_gcd_iff]
  rw [← hmul, hc]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ hg
    calc
      g * r = r * g := mul_comm _ _
      _ = (g * c) * b := hb
      _ = g * (c * b) := mul_assoc _ _ _
  · rintro ⟨b, rfl⟩
    exact ⟨b, by ring⟩


omit [IsDomain R] [IsFractionRing R K] in
/-- Multiplying by the actual denominator ideal yields an integral fractional
ideal. -/
theorem denominatorIdeal_mul_le_one (L : FractionalIdeal R⁰ K) :
    (denominatorIdeal L : FractionalIdeal R⁰ K) * L ≤ 1 := by
  rw [mul_le]
  intro x hx y hy
  obtain ⟨r, hr, rfl⟩ := (mem_coeIdeal R⁰).mp hx
  exact (mem_denominatorIdeal L r).mp hr y hy

/-- The actual integral product of the denominator ideal and the original
fractional ideal. This is the normalized base ideal of fractional coordinates. -/
def denominatorProductIdeal (L : FractionalIdeal R⁰ K) : Ideal R :=
  (((denominatorIdeal L : FractionalIdeal R⁰ K) * L) : Submodule R K).comap (Algebra.linearMap R K)

omit [IsDomain R] [IsFractionRing R K] in
/-- Membership uses the original coefficient map into the original field. -/
theorem mem_denominatorProductIdeal (L : FractionalIdeal R⁰ K) (r : R) :
    r ∈ denominatorProductIdeal L ↔
      algebraMap R K r ∈ (denominatorIdeal L : FractionalIdeal R⁰ K) * L := by
  change algebraMap R K r ∈
    (((denominatorIdeal L : FractionalIdeal R⁰ K) * L) : Submodule R K) ↔ _
  simpa only [coe_mul] using
    (mem_coe (I := (denominatorIdeal L : FractionalIdeal R⁰ K) * L)
      (x := algebraMap R K r))

omit [IsDomain R] [IsFractionRing R K] in
/-- The normalized integral base ideal recovers the literal fractional product. -/
theorem coe_denominatorProductIdeal (L : FractionalIdeal R⁰ K) :
    (denominatorProductIdeal L : FractionalIdeal R⁰ K) =
      (denominatorIdeal L : FractionalIdeal R⁰ K) * L := by
  ext x
  rw [mem_coeIdeal]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_denominatorProductIdeal L r).mp hr
  · intro hx
    obtain ⟨r, hr⟩ := (mem_one_iff R⁰).mp (denominatorIdeal_mul_le_one L hx)
    exact ⟨r, (mem_denominatorProductIdeal L r).mpr (hr.symm ▸ hx), hr⟩

omit [IsDomain R] in
/-- Each original coordinate numerator lies in the actual normalized base ideal. -/
theorem numeratorLinearMap_mem_denominatorProductIdeal (L : FractionalIdeal R⁰ K)
    (x : L) (d : denominatorIdeal L) :
    numeratorLinearMap L x d ∈ denominatorProductIdeal L := by
  rw [mem_denominatorProductIdeal, map_numeratorLinearMap]
  exact mul_mem_mul (mem_coeIdeal_of_mem R⁰ d.property) x.property

omit [IsDomain R] [IsFractionRing R K] in
/-- The original coordinate one embeds the denominator ideal in its normalized
base ideal. -/
theorem denominatorIdeal_le_denominatorProductIdeal (L : FractionalIdeal R⁰ K)
    (hL : (1 : K) ∈ L) : denominatorIdeal L ≤ denominatorProductIdeal L := by
  intro r hr
  rw [mem_denominatorProductIdeal]
  simpa only [mul_one] using mul_mem_mul (mem_coeIdeal_of_mem R⁰ hr) hL

omit [IsDomain R] in
/-- The original numerator map belonging to a specified finite coordinate. -/
def spanFinsetNumeratorLinearMap {ι : Type w} (s : Finset ι) (f : ι → K) (i : s) :
    denominatorIdeal (spanFinset R s f) →ₗ[R] R :=
  numeratorLinearMap (spanFinset R s f) ⟨f i,
    (mem_coe (I := spanFinset R s f)).mp
      (Submodule.subset_span ⟨i.val, i.property, rfl⟩)⟩

omit [IsDomain R] in
/-- The normalized base ideal is generated by the ranges of the original finite
coordinate numerator maps. The denominator is not replaced by a chosen basis. -/
theorem denominatorProductIdeal_spanFinset_eq_iSup_range {ι : Type w}
    (s : Finset ι) (f : ι → K) :
    denominatorProductIdeal (spanFinset R s f) =
      ⨆ i : s, (spanFinsetNumeratorLinearMap s f i).range := by
  classical
  let L := spanFinset R s f
  let J : Ideal R := ⨆ i : s, (spanFinsetNumeratorLinearMap s f i).range
  change denominatorProductIdeal L = J
  apply le_antisymm
  · apply (coeIdeal_le_coeIdeal K).mp
    rw [coe_denominatorProductIdeal, mul_le]
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := (mem_coeIdeal R⁰).mp hx
    have hy' : y ∈ Submodule.span R (f '' (s : Set ι)) :=
      (mem_coe (I := L)).mpr hy
    apply (mem_coe (I := (J : FractionalIdeal R⁰ K))).mp
    refine Submodule.span_induction (s := f '' (s : Set ι))
      (p := fun z _ => algebraMap R K d * z ∈
        ((J : FractionalIdeal R⁰ K) : Submodule R K)) ?_ ?_ ?_ ?_ hy'
    · rintro _ ⟨i, hi, rfl⟩
      let n := spanFinsetNumeratorLinearMap s f ⟨i, hi⟩ ⟨d, hd⟩
      have hn : n ∈ J :=
        (le_iSup (fun i : s => (spanFinsetNumeratorLinearMap s f i).range) ⟨i, hi⟩)
          ⟨⟨d, hd⟩, rfl⟩
      apply (mem_coe (I := (J : FractionalIdeal R⁰ K))).mpr
      exact (mem_coeIdeal R⁰).mpr ⟨n, hn,
        map_numeratorLinearMap L _ ⟨d, hd⟩⟩
    · simpa only [mul_zero] using ((J : FractionalIdeal R⁰ K) : Submodule R K).zero_mem
    · intro y z hy hz ihy ihz
      simpa only [mul_add] using
        ((J : FractionalIdeal R⁰ K) : Submodule R K).add_mem ihy ihz
    · intro r y hy ih
      simpa only [Algebra.smul_def, mul_left_comm] using
        ((J : FractionalIdeal R⁰ K) : Submodule R K).smul_mem r ih
  · apply iSup_le
    intro i r hr
    obtain ⟨d, rfl⟩ := hr
    exact numeratorLinearMap_mem_denominatorProductIdeal L _ d

/-- A principal nonzero denominator ideal produces a primitive base ideal:
no proper principal ideal contains it. The original coordinate one is retained. -/
theorem denominatorProductIdeal_not_le_span_singleton (L : FractionalIdeal R⁰ K)
    (hL : (1 : K) ∈ L) (c : R) (hc : c ≠ 0)
    (hD : denominatorIdeal L = Ideal.span {c}) (p : R) (hp : ¬ IsUnit p) :
    ¬ denominatorProductIdeal L ≤ Ideal.span {p} := by
  intro hN
  have hcD : c ∈ denominatorIdeal L := by
    rw [hD, Ideal.mem_span_singleton]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (hN (denominatorIdeal_le_denominatorProductIdeal L hL hcD))
  have hp₀ : p ≠ 0 := by
    intro hzero
    exact hc (by simpa only [hzero, zero_mul] using ha)
  have hpK : algebraMap R K p ≠ 0 :=
    fun h => hp₀ ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
  have haD : a ∈ denominatorIdeal L := by
    rw [mem_denominatorIdeal]
    intro x hx
    let n := numeratorLinearMap L ⟨x, hx⟩ ⟨c, hcD⟩
    have hn : n ∈ denominatorProductIdeal L :=
      numeratorLinearMap_mem_denominatorProductIdeal L ⟨x, hx⟩ ⟨c, hcD⟩
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hN hn)
    apply (mem_one_iff R⁰).mpr
    refine ⟨b, ?_⟩
    apply mul_left_cancel₀ hpK
    calc
      algebraMap R K p * algebraMap R K b = algebraMap R K (p * b) :=
        (map_mul _ _ _).symm
      _ = algebraMap R K n := by rw [← hb]
      _ = algebraMap R K c * x := map_numeratorLinearMap L ⟨x, hx⟩ ⟨c, hcD⟩
      _ = algebraMap R K p * (algebraMap R K a * x) := by
        rw [ha, map_mul, mul_assoc]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hD ▸ haD)
  have hpb : p * b = 1 := by
    apply mul_left_cancel₀ hc
    calc
      c * (p * b) = p * (c * b) := by ring
      _ = p * a := by rw [← hb]
      _ = c := ha.symm
      _ = c * 1 := (mul_one c).symm
  exact hp (isUnit_iff_dvd_one.mpr ⟨b, hpb.symm⟩)

end FractionalIdeal
