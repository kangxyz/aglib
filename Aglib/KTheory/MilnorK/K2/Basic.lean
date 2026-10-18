/-
Extracted and mechanically adapted from the private, user-owned R5 source:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/Basic.lean
Original Git blob SHA-1: 50f041a15e0cfb0272fb20a84a30a22ff236e951
Original SHA-256: fe9037363f78ceaa75e33db45394bb76deae47cd9118d98d53050f7b40f2f331
No upstream license is declared. This copied implementation is NOT covered by
this standalone project's Apache license statement. This local source reuse
provides no authorization for public redistribution. Original source comments
and attribution are retained below. See THIRD_PARTY_NOTICES.md and LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.GroupWithZero.Units.Basic

-- Preserve the original non-Apache provenance notice rather than invent a license.
set_option linter.style.header false

/-!
# Milnor K₂ of a field

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
-/

@[expose] public section

namespace MilnorK.K2

variable (K : Type*) [Field K]

/-- The field's multiplicative units, written additively for the integer tensor product.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
abbrev UnitsAdd := Additive Kˣ

/-- The tensor presentation before imposing the auxiliary Steinberg relations.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
abbrev UnitTensor := TensorProduct ℤ (UnitsAdd K) (UnitsAdd K)

/-- Steinberg tensors for nonzero `a,b` with `a+b=1`; auxiliary symbol foundations.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def steinbergGenerators : Set (UnitTensor K) :=
  {t | ∃ a b : Kˣ, (a : K) + (b : K) = 1 ∧
    t = TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)}

/-- The integer span of the Steinberg tensors, with no additional relations imposed.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def steinbergSpan : Submodule ℤ (UnitTensor K) :=
  Submodule.span ℤ (steinbergGenerators K)

/-- Milnor K₂ as the actual integer tensor quotient; source scope is documented above.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
abbrev Group := UnitTensor K ⧸ steinbergSpan K

variable {K}

/-- The symbol `{a,b}` in the constructed Milnor group, used by K2-018.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def symbol (a b : Kˣ) : Group K :=
  (steinbergSpan K).mkQ (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b))

variable (K)

/-- The genuine integer-bilinear symbol map arising from the tensor quotient.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def symbolBilinear : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] Group K :=
  (TensorProduct.mk ℤ (UnitsAdd K) (UnitsAdd K)).compr₂ (steinbergSpan K).mkQ

variable {K}

/-- The bilinear map evaluates to the constructed symbol.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem symbolBilinear_apply (a b : Kˣ) :
    symbolBilinear K (Additive.ofMul a) (Additive.ofMul b) = symbol a b := rfl

/-- Multiplicative bilinearity in the first field argument.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_mul_left (a b c : Kˣ) :
    symbol (a * b) c = symbol a c + symbol b c := by
  change (steinbergSpan K).mkQ
    (TensorProduct.tmul ℤ (Additive.ofMul a + Additive.ofMul b) (Additive.ofMul c)) = _
  rw [TensorProduct.add_tmul, map_add]
  rfl

/-- Multiplicative bilinearity in the second field argument.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_mul_right (a b c : Kˣ) :
    symbol a (b * c) = symbol a b + symbol a c := by
  change (steinbergSpan K).mkQ
    (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b + Additive.ofMul c)) = _
  rw [TensorProduct.tmul_add, map_add]
  rfl

/-- A symbol with first entry one vanishes; auxiliary symbol algebra.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem symbol_one_left (a : Kˣ) : symbol 1 a = 0 := by
  simp [symbol]

/-- A symbol with second entry one vanishes; auxiliary symbol algebra.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem symbol_one_right (a : Kˣ) : symbol a 1 = 0 := by
  simp [symbol]

/-- Inverting the first entry negates the symbol.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem symbol_inv_left (a b : Kˣ) : symbol a⁻¹ b = -symbol a b := by
  simp [symbol, ofMul_inv, TensorProduct.neg_tmul]

/-- Inverting the second entry negates the symbol.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem symbol_inv_right (a b : Kˣ) : symbol a b⁻¹ = -symbol a b := by
  simp [symbol, ofMul_inv, TensorProduct.tmul_neg]

/-- Division expands as subtraction in the first entry.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_div_left (a b c : Kˣ) : symbol (a / b) c = symbol a c - symbol b c := by
  rw [div_eq_mul_inv, symbol_mul_left, symbol_inv_left, sub_eq_add_neg]

/-- Division expands as subtraction in the second entry.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem symbol_div_right (a b c : Kˣ) : symbol a (b / c) = symbol a b - symbol a c := by
  rw [div_eq_mul_inv, symbol_mul_right, symbol_inv_right, sub_eq_add_neg]

/-- The Steinberg relation is proved in the actual quotient, not supplied as an axiom.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem steinberg (a b : Kˣ) (h : (a : K) + (b : K) = 1) : symbol a b = 0 := by
  change (Submodule.Quotient.mk
    (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)) : Group K) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨a, b, h, rfl⟩

variable {A : Type*} [AddCommGroup A]

/-- A bilinear map killing Steinberg tensors descends to the constructed Milnor quotient.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def lift (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) : Group K →ₗ[ℤ] A :=
  (steinbergSpan K).liftQ (TensorProduct.lift b) (by
    rw [steinbergSpan, Submodule.span_le]
    rintro t ⟨a, c, hac, rfl⟩
    exact hb a c hac)

/-- The descended map has its prescribed symbol values.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem lift_symbol (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) (a c : Kˣ) :
    lift b hb (symbol a c) = b (Additive.ofMul a) (Additive.ofMul c) := rfl

/-- Integer-linear maps out of Milnor K₂ are determined by all symbols.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[ext] theorem linearMap_ext (f g : Group K →ₗ[ℤ] A)
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro a b
  exact h a.toMul b.toMul

/-- Additive maps out of Milnor K₂ are determined by all symbols.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[ext] theorem addHom_ext (f g : Group K →+ A)
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact linearMap_ext f.toIntLinearMap g.toIntLinearMap h

/-- The universal property of the actual Milnor presentation, including uniqueness.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem existsUnique_lift (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) :
    ∃! f : Group K →ₗ[ℤ] A, ∀ a c : Kˣ,
      f (symbol a c) = b (Additive.ofMul a) (Additive.ofMul c) := by
  refine ⟨lift b hb, fun a c => lift_symbol b hb a c, ?_⟩
  intro f hf
  exact linearMap_ext f (lift b hb) (fun a c => (hf a c).trans (lift_symbol b hb a c).symm)

end MilnorK.K2
