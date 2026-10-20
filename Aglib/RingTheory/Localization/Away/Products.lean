/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.Tactic.Ring

/-!
# Finite products of principal localizations


Source: `R5Lab.Aglib.RingTheory.Localization.Away.Products`.
Packet SHA-256:
`dec037df2aa97b1847f6d59b6847b35a3256eac2c32568a0b32d8406520d18f2`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
universe u

namespace Localization.Away

variable (R S : Type u) [CommRing R] [CommRing S]
variable [Algebra R S] (r : R) [IsLocalization.Away r S]

/-- The product of two localizations is the localization of the product at
its diagonal denominator. Common denominators are proved, not assumed. -/
instance productAlgebra : Algebra (R × R) (S × S) :=
  ((algebraMap R S).prodMap (algebraMap R S)).toAlgebra

instance diagonalLocalization : IsLocalization.Away (r, r) (S × S) := by
  apply IsLocalization.Away.mk
  · exact Prod.isUnit_iff.mpr ⟨IsLocalization.Away.algebraMap_isUnit r,
      IsLocalization.Away.algebraMap_isUnit r⟩
  · rintro ⟨x, y⟩
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj r x
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r y
    refine ⟨m + n, (a * r ^ n, b * r ^ m), ?_⟩
    apply Prod.ext
    · change x * (algebraMap R S r) ^ (m + n) = algebraMap R S (a * r ^ n)
      rw [pow_add, ← mul_assoc, ha, map_mul, map_pow]
    · change y * (algebraMap R S r) ^ (m + n) = algebraMap R S (b * r ^ m)
      rw [Nat.add_comm m n, pow_add, ← mul_assoc, hb, map_mul, map_pow]
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq r (congrArg Prod.fst h)
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq r (congrArg Prod.snd h)
    change r ^ m * a = r ^ m * c at hm
    change r ^ n * b = r ^ n * d at hn
    refine ⟨m + n, ?_⟩
    apply Prod.ext
    · change r ^ (m + n) * a = r ^ (m + n) * c
      calc
        _ = r ^ n * (r ^ m * a) := by rw [pow_add]; ring
        _ = r ^ n * (r ^ m * c) := by rw [hm]
        _ = _ := by rw [pow_add]; ring
    · change r ^ (m + n) * b = r ^ (m + n) * d
      calc
        _ = r ^ m * (r ^ n * b) := by rw [pow_add]; ring
        _ = r ^ m * (r ^ n * d) := by rw [hn]
        _ = _ := by rw [pow_add]; ring

/-- For a supplied localization S of R away from r, the canonical equivalence between
localization at the diagonal denominator and the product of the two localizations. -/
def productLocalizationEquiv : Localization.Away (r, r) ≃ₐ[R × R] (S × S) :=
  IsLocalization.algEquiv (Submonoid.powers (r, r)) _ _

theorem productLocalizationEquiv_algebraMap (p : R × R) :
    productLocalizationEquiv R S r (algebraMap (R × R) (Localization.Away (r, r)) p) =
      (algebraMap R S p.1, algebraMap R S p.2) :=
  (productLocalizationEquiv R S r).commutes p

end Localization.Away

namespace Localization.Away

section FiniteProducts
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (r : R) [IsLocalization.Away r S] (n : ℕ)

/-- A finite product of the same principal localization, with the actual
pointwise algebra structure, is localization at the diagonal denominator. -/
instance finitePiLocalization : IsLocalization.Away (fun _ : Fin n => r) (Fin n → S) := by
  apply (IsLocalization.iff_map_piEvalRingHom (fun _ : Fin n => R)
    (Fin n → S) (Submonoid.powers (fun _ : Fin n => r))).mpr
  have (i : Fin n) : IsLocalization
      ((Submonoid.powers (fun _ : Fin n => r)).map (Pi.evalRingHom (fun _ => R) i)) S := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away r S)
  infer_instance

end FiniteProducts

end Localization.Away
