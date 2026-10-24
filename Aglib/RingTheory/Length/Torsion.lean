/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length

/-!
# Length bounds for torsion by products and powers

Multiplication by `d` maps the original `(b * d)`-torsion into the original
`b`-torsion, with kernel the original `d`-torsion. Exact length additivity
through its actual image gives a product bound and hence bounds for powers.
The ambient module is arbitrary; lengths take values in `ℕ∞`.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Torsion by a product has length bounded by the sum of the two original
torsion lengths. The multiplication map is used through its actual image. -/
theorem length_torsionBy_mul_le (b d : R) :
    Module.length R (torsionBy R M (b * d)) ≤
      Module.length R (torsionBy R M d) + Module.length R (torsionBy R M b) := by
  let φ : torsionBy R M (b * d) →ₗ[R] torsionBy R M b :=
    { toFun := fun x => ⟨d • (x : M), by
        change b • (d • (x : M)) = 0
        rw [← mul_smul]
        exact x.property⟩
      map_add' := fun x y => Subtype.ext (smul_add d (x : M) (y : M))
      map_smul' := fun r x => Subtype.ext (smul_comm d r (x : M)) }
  have hd : torsionBy R M d ≤ torsionBy R M (b * d) := by
    intro x hx
    change d • x = 0 at hx
    change (b * d) • x = 0
    rw [mul_smul, hx, smul_zero]
  have hexact : Function.Exact (inclusion hd) φ.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hdx := congrArg (fun y : LinearMap.range φ => (y.1 : M)) hx
      change d • (x : M) = 0 at hdx
      refine ⟨⟨(x : M), hdx⟩, ?_⟩
      exact Subtype.ext rfl
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (Subtype.ext y.property)
  calc
    Module.length R (torsionBy R M (b * d)) =
        Module.length R (torsionBy R M d) + Module.length R (LinearMap.range φ) :=
      Module.length_eq_add_of_exact (inclusion hd) φ.rangeRestrict
        (inclusion_injective hd) (LinearMap.surjective_rangeRestrict φ) hexact
    _ ≤ Module.length R (torsionBy R M d) + Module.length R (torsionBy R M b) :=
      add_le_add_right (Module.length_le_of_injective (LinearMap.range φ).subtype
        (subtype_injective _)) _

/-- Torsion by the `r`th power has length at most `r` times the original
scalar-torsion length, without a finiteness assumption on the ambient module. -/
theorem length_torsionBy_pow_le (c : R) (r : ℕ) :
    Module.length R (torsionBy R M (c ^ r)) ≤
      (r : ℕ∞) * Module.length R (torsionBy R M c) := by
  induction r with
  | zero =>
    calc
      Module.length R (torsionBy R M (c ^ 0)) = 0 := by
        rw [_root_.pow_zero, torsionBy_one, Module.length_bot]
      _ ≤ (0 : ℕ∞) * Module.length R (torsionBy R M c) := zero_le
  | succ r ih =>
    calc
      Module.length R (torsionBy R M (c ^ (r + 1))) ≤
          Module.length R (torsionBy R M c) +
            Module.length R (torsionBy R M (c ^ r)) := by
        rw [_root_.pow_succ]
        exact length_torsionBy_mul_le (M := M) (c ^ r) c
      _ ≤ Module.length R (torsionBy R M c) +
          (r : ℕ∞) * Module.length R (torsionBy R M c) := add_le_add_right ih _
      _ = (r : ℕ∞) * Module.length R (torsionBy R M c) +
          Module.length R (torsionBy R M c) := _root_.add_comm _ _
      _ = ((r + 1 : ℕ) : ℕ∞) * Module.length R (torsionBy R M c) := by
        rw [Nat.cast_add, Nat.cast_one, _root_.add_mul, _root_.one_mul]

/-- Divisibility by a power bounds the original `a`-torsion using the
original `c`-torsion in the same module and with the same scalar action. -/
theorem length_torsionBy_le_of_dvd_pow (a c : R) (r : ℕ) (h : a ∣ c ^ r) :
    Module.length R (torsionBy R M a) ≤
      (r : ℕ∞) * Module.length R (torsionBy R M c) := by
  have hle : torsionBy R M a ≤ torsionBy R M (c ^ r) :=
    torsionBy_le_torsionBy_of_dvd a (c ^ r) h
  exact (Module.length_le_of_injective (inclusion hle)
    (inclusion_injective hle)).trans (length_torsionBy_pow_le c r)

end Submodule
