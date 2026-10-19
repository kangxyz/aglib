/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Support

/-!
# Spreading regularity from a prime to a principal open

`IsNoetherianRing.exists_away_isSMulRegular_of_atPrime`: over a Noetherian ring `S`, if `a` is
regular in the local ring at a prime `q`, then `a` is regular in `S_f` for some `f ∉ q`. The
kernel of multiplication by `a` is a finite module whose localization at `q` vanishes, so it
vanishes after inverting one element (`LocalizedModule.exists_subsingleton_away`). The consumer
is the pointwise fiber criterion for relative effective Cartier divisors.
-/

@[expose] public section

noncomputable section

/-- Over a Noetherian ring, regularity at a prime spreads to a principal open neighbourhood. -/
theorem IsNoetherianRing.exists_away_isSMulRegular_of_atPrime {S : Type*} [CommRing S]
    [IsNoetherianRing S] (a : S) (q : Ideal S) [q.IsPrime]
    (ha : IsSMulRegular (Localization.AtPrime q) (algebraMap S (Localization.AtPrime q) a)) :
    ∃ f ∉ q, IsSMulRegular (Localization.Away f) (algebraMap S (Localization.Away f) a) := by
  let K := LinearMap.ker (LinearMap.mulLeft S a)
  have hK (k : S) (hk : k ∈ K) : a * k = 0 := hk
  have : Subsingleton (LocalizedModule q.primeCompl K) := by
    rw [LocalizedModule.subsingleton_iff]
    rintro ⟨k, hk⟩
    have h0 : algebraMap S (Localization.AtPrime q) k = 0 := by
      apply ha
      simp only [smul_eq_mul, mul_zero, ← map_mul, hK k hk, map_zero]
    obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ k).mp h0
    exact ⟨u, hu, Subtype.ext (by simpa using hu')⟩
  obtain ⟨f, hf, hsub⟩ := LocalizedModule.exists_subsingleton_away (M := K) q
  refine ⟨f, hf, ?_⟩
  have key (z : Localization.Away f) (hz : algebraMap S (Localization.Away f) a * z = 0) :
      z = 0 := by
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    dsimp only at hz ⊢
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨m, hm⟩ := hz
    have hmc : (m : S) * c ∈ K := by
      change a * ((m : S) * c) = 0
      rw [mul_left_comm]
      exact hm
    obtain ⟨r, hr, hr'⟩ := (LocalizedModule.subsingleton_iff.mp hsub) ⟨_, hmc⟩
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨r * m, Submonoid.mul_mem _ hr m.2⟩, ?_⟩
    have := congrArg Subtype.val hr'
    simp only [Submodule.coe_smul_of_tower, smul_eq_mul, Submodule.coe_zero] at this
    change r * (m : S) * c = 0
    rw [mul_assoc]
    exact this
  intro x y hxy
  have h : algebraMap S (Localization.Away f) a * (x - y) = 0 := by
    rw [mul_sub]
    exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (key _ h)

