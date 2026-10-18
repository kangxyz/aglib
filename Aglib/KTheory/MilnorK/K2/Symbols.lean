/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.Basic
public import Mathlib.Tactic.Ring

/-!
# Symbol identities and additive lifts for Milnor K₂

The group `K2 K` is the quotient of
`Additive Kˣ ⊗[ℤ] Additive Kˣ` by the integer span of the Steinberg tensors.
Its symbols are constructed from the tensor quotient. Bilinearity, Steinberg,
the universal property, field functoriality, and sign identities are proved
from this presentation, with no external mathematical premise. Functoriality
and further symbol identities are in the `Map` and `Symbols` modules.

## Source correspondence

Source file: `research/exposes/K2/018/expose.tex`,
`K2-018#sec:k2018-introduction`, lines 63–82, and
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This identity applies to every declaration below.

Formalized scope: auxiliary algebraic foundations for the field symbols used
in the introduction and residue calculation. The introduction's identification
with Quillen field K₂ requires Matsumoto as a separate background theorem;
no Quillen group or Matsumoto comparison is defined here. This module makes
no assertion about arithmetic model images, origin specialization, motivic
comparison, or cohomological Bocksteins.

## Implementation provenance

Original R5 implementation:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/Symbols.lean
Original Git blob SHA-1: `e4d139520b5bdd10bbe4cab79c5ee71b97f2d945`.
Original SHA-256: `cbce55a1358e59c4a0ef965dd90603023069b5674692ce98017096d7c22b408c`.
-/

@[expose] public section

namespace MilnorK.K2

variable (K : Type*) [Field K]

variable {K}

variable {A : Type*} [AddCommGroup A]

variable {L : Type*} [Field L]

variable {M : Type*} [Field M]

/-- The unit `1-a`, whose nonzero condition is proved from `a≠1`.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
noncomputable def oneSub (a : Kˣ) (ha : a ≠ 1) : Kˣ :=
  Units.mk0 (1 - (a : K)) (by
    intro hz
    apply ha
    apply Units.ext
    exact (sub_eq_zero.mp hz).symm)

/-- The auxiliary `oneSub` unit has the expected field value.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem oneSub_coe (a : Kˣ) (ha : a ≠ 1) :
    (oneSub a ha : K) = 1 - (a : K) := rfl

/-- The customary `{a,1-a}=0` form of Steinberg for nonzero field entries.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_oneSub (a : Kˣ) (ha : a ≠ 1) : symbol a (oneSub a ha) = 0 := by
  apply steinberg
  simp only [oneSub_coe]
  ring

/-- `{a,-a}=0`, derived solely from bilinearity and Steinberg.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_self_neg (a : Kˣ) : symbol a (-a) = 0 := by
  by_cases ha : a = 1
  · subst a
    exact symbol_one_left _
  have hai : a⁻¹ ≠ 1 := by simpa using ha
  have hleft := symbol_oneSub a ha
  have hright : symbol a (oneSub a⁻¹ hai) = 0 := by
    have h := symbol_oneSub a⁻¹ hai
    rw [symbol_inv_left] at h
    exact neg_eq_zero.mp h
  have heq : oneSub a ha = (-a) * oneSub a⁻¹ hai := by
    apply Units.ext
    simp only [oneSub_coe, Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
    rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ a.ne_zero]
    ring
  rw [heq, symbol_mul_right, hright, add_zero] at hleft
  exact hleft

/-- `{a,a}={a,-1}`, derived from the preceding sign relation and two-torsion.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_self (a : Kˣ) : symbol a a = symbol a (-1) := by
  have h := symbol_self_neg a
  rw [show -a = a * (-1) by simp, symbol_mul_right] at h
  have hsign : symbol a (-1) + symbol a (-1) = 0 := by
    rw [← symbol_mul_right]
    simp
  exact (eq_neg_of_add_eq_zero_left h).trans (eq_neg_of_add_eq_zero_left hsign).symm

/-- Skew symmetry is proved from the Steinberg presentation rather than imposed on it.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_skew (a b : Kˣ) : symbol a b = -symbol b a := by
  have hab := symbol_self_neg (a * b)
  have ha := symbol_self_neg a
  have hb := symbol_self_neg b
  rw [show -(a * b) = (-a) * b by simp, symbol_mul_left,
    symbol_mul_right, symbol_mul_right, ha, zero_add] at hab
  rw [show -a = a * (-1) by simp, symbol_mul_right] at hab
  rw [show -b = b * (-1) by simp, symbol_mul_right] at hb
  have hcross : symbol a b + symbol b a = 0 := by
    calc
      symbol a b + symbol b a =
        (symbol a b + ((symbol b a + symbol b (-1)) + symbol b b)) -
          (symbol b b + symbol b (-1)) := by abel
      _ = 0 := by rw [hab, hb, sub_self]
  exact eq_neg_of_add_eq_zero_left hcross

/-!
## Symbol-function convenience interface

The declarations below retain the tensor quotient `K2 K` and its universal
property. Their auxiliary symbol-algebra source is
`K2-018#sec:k2018-introduction` at the module snapshot documented above.
The convenience interface is adapted from `WeightTwoBockstein/MilnorK2.lean`
in delivered source revision `39cf3ab`, file SHA-256
`78230009a78cdf0d706340a67b8d6a149d1d230b0e424c1476251aeb17136133`.
Its free-abelian presentation is not introduced here.
-/

variable {A : Type*} [AddCommGroup A]

/-- A two-entry function satisfying the bilinearity and Steinberg relations.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
structure SymbolMap where
  /-- The proposed symbol value on an ordered pair of field units. -/
  toFun : Kˣ → Kˣ → A
  mul_left : ∀ a b c, toFun (a * b) c = toFun a c + toFun b c
  mul_right : ∀ a b c, toFun a (b * c) = toFun a b + toFun a c
  steinberg : ∀ (a b : Kˣ), (a : K) + (b : K) = 1 → toFun a b = 0

/-- Convert a symbol function to the integer-bilinear input for the tensor lift.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def symbolMapBilinear (s : SymbolMap (K := K) (A := A)) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A :=
  ({
    toFun := fun a => ({
      toFun := fun b => s.toFun a.toMul b.toMul
      map_zero' := by
        change s.toFun a.toMul 1 = 0
        have h := s.mul_right a.toMul 1 1
        exact (add_left_cancel (show s.toFun a.toMul 1 + 0 =
          s.toFun a.toMul 1 + s.toFun a.toMul 1 by
            simpa only [one_mul, add_zero] using h)).symm
      map_add' := fun b c => s.mul_right a.toMul b.toMul c.toMul
    } : UnitsAdd K →+ A).toIntLinearMap
    map_zero' := by
      apply LinearMap.ext
      intro b
      change s.toFun 1 b.toMul = 0
      have h := s.mul_left 1 1 b.toMul
      exact (add_left_cancel (show s.toFun 1 b.toMul + 0 =
        s.toFun 1 b.toMul + s.toFun 1 b.toMul by
          simpa only [one_mul, add_zero] using h)).symm
    map_add' := by
      intro a c
      apply LinearMap.ext
      intro b
      exact s.mul_left a.toMul c.toMul b.toMul
  } : UnitsAdd K →+ (UnitsAdd K →ₗ[ℤ] A)).toIntLinearMap

/-- Extend a symbol function through the existing tensor quotient as an additive map.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
def liftSymbols (s : SymbolMap (K := K) (A := A)) : Group K →+ A :=
  (lift (symbolMapBilinear s) (by
    intro a b hab
    exact s.steinberg a b hab)).toAddMonoidHom

/-- The additive tensor lift takes the prescribed values on symbols.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem liftSymbols_symbol (s : SymbolMap (K := K) (A := A)) (a b : Kˣ) :
    liftSymbols s (symbol a b) = s.toFun a b := rfl

/-- Additive maps out of the tensor quotient are determined by their symbol values.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[ext] theorem symbolHom_ext {f g : Group K →+ A}
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g :=
  addHom_ext f g h

/-- Uniqueness of the additive map extending a symbol function.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem liftSymbols_unique (s : SymbolMap (K := K) (A := A)) (f : Group K →+ A)
    (h : ∀ a b : Kˣ, f (symbol a b) = s.toFun a b) : f = liftSymbols s := by
  apply symbolHom_ext
  intro a b
  rw [h, liftSymbols_symbol]

/-- Natural powers in the first entry act by repeated addition.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
theorem symbol_pow_left (a b : Kˣ) (n : ℕ) :
    symbol (a ^ n) b = n • symbol a b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, symbol_mul_left, ih, succ_nsmul]

/-- Natural powers in the second entry act by repeated addition.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
theorem symbol_pow_right (a b : Kˣ) (n : ℕ) :
    symbol a (b ^ n) = n • symbol a b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, symbol_mul_right, ih, succ_nsmul]

/-- A root of unity in the first entry gives a torsion symbol.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
theorem nsmul_symbol_eq_zero_of_pow_eq_one (a b : Kˣ) (n : ℕ) (h : a ^ n = 1) :
    n • symbol a b = 0 := by
  rw [← symbol_pow_left, h, symbol_one_left]

/-- A root of unity in the second entry gives a torsion symbol.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above; convenience interface as identified above. -/
theorem nsmul_symbol_eq_zero_of_pow_eq_one_right (a b : Kˣ) (n : ℕ) (h : b ^ n = 1) :
    n • symbol a b = 0 := by
  rw [← symbol_pow_right, h, symbol_one_right]

end MilnorK.K2
