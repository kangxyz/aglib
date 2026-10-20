/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fields with a supplied divisor map

Source: `R5Lab.Aglib.FieldTheory.Divisors.Basic`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

namespace Field
variable {C K Div : Type*} [Field C] [Field K] [AddCommGroup Div]
/-- General function-field divisor background: kernel of the divisor map is
exactly the embedded constant units. No symbol theorem is included as data.
Source: the proper connected curve and function-divisor background in
`K2-018#lem:k2018-geometric-exact-order`, at the documented source snapshot. -/
structure DivisorData (C K Div : Type*) [Field C] [Field K] [AddCommGroup Div] where
  constants : C →+* K
  divisor : Additive Kˣ →+ Div
  kernel_eq_constants : ∀ f : Kˣ, divisor (Additive.ofMul f) = 0 ↔
    ∃ a : Cˣ, Units.map constants.toMonoidHom a = f

namespace DivisorData

variable (d : DivisorData C K Div)

/-- The constant unit embedded in the function field.
Source: the constant inclusion used in `K2-018#lem:k2018-geometric-exact-order`;
this is auxiliary field algebra at the documented source snapshot. -/
abbrev constant (a : Cˣ) : Kˣ := Units.map d.constants.toMonoidHom a

/-- The embedded constant one is one.
Source: auxiliary field algebra for `K2-018#lem:k2018-geometric-exact-order`,
at the documented source snapshot. -/
@[simp] theorem constant_one : d.constant 1 = 1 := map_one _

/-- Constant embedding preserves natural powers.
Source: auxiliary root-symbol algebra for `K2-018#lem:k2018-geometric-exact-order`,
at the documented source snapshot. -/
@[simp] theorem constant_pow (a : Cˣ) (n : ℕ) :
    d.constant (a ^ n) = d.constant a ^ n := map_pow _ a n

/-- Constant embedding preserves integer powers, including negative exponents.
Source: auxiliary algebra for the integer-coprime version of
`K2-018#lem:k2018-geometric-exact-order`, at the documented source snapshot. -/
@[simp] theorem constant_zpow (a : Cˣ) (n : ℤ) :
    d.constant (a ^ n) = d.constant a ^ n := map_zpow _ a n

/-- A field homomorphism embeds constant units injectively.
Source: the constant-field background of `K2-018#lem:k2018-geometric-exact-order`;
this auxiliary implication is proved at the documented source snapshot. -/
theorem constant_injective : Function.Injective d.constant := by
  intro a b h
  apply Units.ext
  exact d.constants.injective (congrArg (fun a : Kˣ => (a : K)) h)

/-- The embedded root has exactly the same multiplicative order as the constant.
Source: primitive roots in `K2-018#lem:k2018-geometric-exact-order`;
this auxiliary order statement is proved at the documented source snapshot. -/
@[simp] theorem orderOf_constant (a : Cˣ) :
    orderOf (d.constant a) = orderOf a :=
  orderOf_injective (Units.map d.constants.toMonoidHom) d.constant_injective a

/-- The actual additive divisor quotient by principal divisors.
Source: the divisor-class group underlying `[D]` in
`K2-018#lem:k2018-geometric-exact-order`, at the documented source snapshot.
Identification with the curve's Picard group is a separate background realization. -/
abbrev ClassGroup := Div ⧸ d.divisor.range

/-- The quotient homomorphism from divisors to divisor classes.
Source: `[D]` in `K2-018#lem:k2018-geometric-exact-order`,
at the documented source snapshot. -/
def classMap : Div →+ d.ClassGroup := QuotientAddGroup.mk' d.divisor.range

/-- A divisor class is zero precisely when the divisor is that of a function.
Source: choosing `g` in `K2-018#lem:k2018-geometric-exact-order`, line 380;
this follows from the actual quotient, at the documented source snapshot. -/
theorem classMap_eq_zero_iff (D : Div) :
    d.classMap D = 0 ↔ ∃ f : Kˣ, d.divisor (Additive.ofMul f) = D := by
  change (D : Div ⧸ d.divisor.range) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toMul, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨Additive.ofMul f, hf⟩

/-- Constant functions have zero divisor, derived from the kernel background.
Source: constant factors in `K2-018#lem:k2018-geometric-exact-order`,
at the documented source snapshot. -/
@[simp] theorem divisor_constant (a : Cˣ) :
    d.divisor (Additive.ofMul (d.constant a)) = 0 :=
  (d.kernel_eq_constants _).2 ⟨a, rfl⟩

/-- The divisor of a natural power is the scalar multiple of its divisor.
Source: the power factorizations in `K2-018#lem:k2018-geometric-exact-order`;
this is proved from the divisor homomorphism at the documented source snapshot. -/
@[simp] theorem divisor_pow (f : Kˣ) (n : ℕ) :
    d.divisor (Additive.ofMul (f ^ n)) = n • d.divisor (Additive.ofMul f) := by
  rw [ofMul_pow, map_nsmul]

end DivisorData

end Field
