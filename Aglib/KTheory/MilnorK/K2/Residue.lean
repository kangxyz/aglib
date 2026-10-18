/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.Symbols
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Tame symbols from discrete valuation and residue data

This module constructs a map out of the genuine Milnor K₂ tensor quotient.
The raw signed valuation formula is proved bilinear and Steinberg before it
is descended. In multiplicative notation its convention is `∂{u,π}=ū`.

## Source correspondence

Source file: `research/exposes/K2/018/expose.tex`,
`K2-018#sec:k2018-introduction`, lines 63–82, and
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This identity applies to every declaration below.

`DiscreteResidueData` is an explicit background interface for a normalized DVR
with fraction field `K`, residue field `k`, valuation `v`, and uniformizer `π`.
Its `unitPart(a)` is the additive notation for the reduction of `a π^(-v(a))`.
Both `v` and the residue-unit-part map are group homomorphisms. The interface
also supplies the elementary local identities for `a+b=1`: when `v(a)>0`,
`v(b)=0` and the residue of `b` is one; when `v(a)<0`, `v(b)=v(a)` and the
residue unit part of `b` is that of `a` multiplied by the residue of `-1`.
In `UnitsAdd k`, this is addition of `residueSign k`. These are valuation
and reduction statements, not a Steinberg assertion about the tame formula.
No symbol map, descended map, or tame-symbol theorem is supplied as data.

Formalized scope: the auxiliary construction/descent, normalization convention,
and vanishing of tame symbols on residue-characteristic-primary torsion.
Constructing this decomposition from a concrete DVR remains a background
realization obligation. The identification with Quillen field K₂ needs the
separate Matsumoto premise. The source's equality with a cohomological residue,
motivic coefficient product rule, and arithmetic integrality remain outside
this module.

## Implementation provenance

Original R5 implementation:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/Residue.lean
Original Git blob SHA-1: `e7b6f75478320a087e11e7476e06ab96387fcc3f`.
Original SHA-256: `6ff41c485e14afbe170e6c00507e3fd7600bb70851b09c1b8b8245faae048244`.
-/

@[expose] public section

namespace MilnorK.K2

variable {K k : Type*} [Field K] [Field k]

/-- Additive notation for the residue sign `-1` in the source's tame-symbol formula.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
def residueSign (k : Type*) [Field k] : UnitsAdd k := Additive.ofMul (-1)

/-- The sign is killed by two, including in residue characteristic two.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem residueSign_add_self : residueSign k + residueSign k = 0 := by
  change Additive.ofMul ((-1 : kˣ) * (-1)) = 0
  simp

/-- Explicit normalized valuation/residue background; its semantic scope is detailed above.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
structure DiscreteResidueData (K k : Type*) [Field K] [Field k] where
  /-- The specified integer-valued valuation homomorphism. -/
  value : UnitsAdd K →ₗ[ℤ] ℤ
  /-- The specified additive residue-unit-part homomorphism. -/
  unitPart : UnitsAdd K →ₗ[ℤ] UnitsAdd k
  /-- The specified field unit whose valuation is one. -/
  uniformizer : Kˣ
  value_uniformizer : value (Additive.ofMul uniformizer) = 1
  unitPart_uniformizer : unitPart (Additive.ofMul uniformizer) = 0
  unitPart_neg_one : unitPart (Additive.ofMul (-1)) = residueSign k
  positive : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → 0 < value (Additive.ofMul a) →
    value (Additive.ofMul b) = 0 ∧ unitPart (Additive.ofMul b) = 0
  negative : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → value (Additive.ofMul a) < 0 →
    value (Additive.ofMul b) = value (Additive.ofMul a) ∧
      unitPart (Additive.ofMul b) = unitPart (Additive.ofMul a) + residueSign k

/-- The signed tame formula before proving bilinearity or descent.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
def rawTame (d : DiscreteResidueData K k) (a b : UnitsAdd K) : UnitsAdd k :=
  (d.value a * d.value b) • residueSign k + d.value b • d.unitPart a -
    d.value a • d.unitPart b

/-- Bilinearity of the signed formula, proved from the two homomorphisms in the data.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
def tameBilinear (d : DiscreteResidueData K k) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] UnitsAdd k :=
  LinearMap.mk₂ ℤ (rawTame d)
    (by
      intro a b c
      simp only [rawTame, map_add, add_mul, add_zsmul, zsmul_add]
      abel)
    (by
      intro r a b
      simp [rawTame, map_smul, smul_add, smul_sub, smul_smul,
        mul_comm, mul_left_comm])
    (by
      intro a b c
      simp only [rawTame, map_add, mul_add, add_zsmul, zsmul_add]
      abel)
    (by
      intro r a b
      simp [rawTame, map_smul, smul_add, smul_sub, smul_smul,
        mul_comm, mul_left_comm])

/-- A sign killed by two is killed by every integer `m²-m`; auxiliary residue algebra.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem square_sub_smul_eq_zero {A : Type*} [AddCommGroup A]
    (x : A) (hx : x + x = 0) (m : ℤ) : (m * m - m) • x = 0 := by
  have htwo : (2 : ℤ) • x = 0 := by simpa only [two_smul] using hx
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro z hz
    have heq : ((z : ℤ) + 1) * ((z : ℤ) + 1) - ((z : ℤ) + 1) =
        ((z : ℤ) * (z : ℤ) - (z : ℤ)) + (z : ℤ) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]
  · intro z hz
    have heq : (-(z : ℤ) - 1) * (-(z : ℤ) - 1) - (-(z : ℤ) - 1) =
        (-(z : ℤ) * -(z : ℤ) - -(z : ℤ)) + (1 + (z : ℤ)) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]

/-- Steinberg is derived from elementary positive/negative valuation cases and sign parity.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem rawTame_steinberg (d : DiscreteResidueData K k) (a b : Kˣ)
    (hab : (a : K) + (b : K) = 1) : rawTame d (Additive.ofMul a) (Additive.ofMul b) = 0 := by
  rcases lt_trichotomy (d.value (Additive.ofMul a)) 0 with hneg | hzero | hpos
  · obtain ⟨hvb, hub⟩ := d.negative a b hab hneg
    calc
      rawTame d (Additive.ofMul a) (Additive.ofMul b) =
        (d.value (Additive.ofMul a) * d.value (Additive.ofMul a)) • residueSign k +
          d.value (Additive.ofMul a) • d.unitPart (Additive.ofMul a) -
          d.value (Additive.ofMul a) •
            (d.unitPart (Additive.ofMul a) + residueSign k) := by rw [rawTame, hvb, hub]
      _ = (d.value (Additive.ofMul a) * d.value (Additive.ofMul a) -
          d.value (Additive.ofMul a)) • residueSign k := by
        rw [zsmul_add, sub_zsmul]
        abel
      _ = 0 := square_sub_smul_eq_zero (residueSign k) residueSign_add_self _
  · rcases lt_trichotomy (d.value (Additive.ofMul b)) 0 with hbneg | hbzero | hbpos
    · obtain ⟨hva, _⟩ := d.negative b a (by simpa [add_comm] using hab) hbneg
      have hvb : d.value (Additive.ofMul b) = 0 := hva.symm.trans hzero
      simp [rawTame, hzero, hvb]
    · simp [rawTame, hzero, hbzero]
    · obtain ⟨_, hua⟩ := d.positive b a (by simpa [add_comm] using hab) hbpos
      simp [rawTame, hzero, hua]
  · obtain ⟨hvb, hub⟩ := d.positive a b hab hpos
    simp [rawTame, hvb, hub]

/-- The actual descended tame homomorphism, after proving bilinearity and Steinberg.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
def tame (d : DiscreteResidueData K k) : Group K →ₗ[ℤ] UnitsAdd k :=
  lift (tameBilinear d) (fun a b hab => rawTame_steinberg d a b hab)

/-- The descended map evaluates to the raw formula on every symbol.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
@[simp] theorem tame_symbol (d : DiscreteResidueData K k) (a b : Kˣ) :
    tame d (symbol a b) = rawTame d (Additive.ofMul a) (Additive.ofMul b) := rfl

/-- The tame homomorphism written with multiplicative residue units as target.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
def tameValue (d : DiscreteResidueData K k) (x : Group K) : kˣ := (tame d x).toMul

/-- The zero Milnor class has tame value one.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
@[simp] theorem tameValue_zero (d : DiscreteResidueData K k) : tameValue d 0 = 1 := by
  change (tame d 0).toMul = 1
  rw [map_zero]
  rfl

/-- Addition of Milnor classes becomes multiplication of residue units.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tameValue_add (d : DiscreteResidueData K k) (x y : Group K) :
    tameValue d (x + y) = tameValue d x * tameValue d y := by
  change (tame d (x + y)).toMul = _
  rw [map_add]
  rfl

/-- The standard sign-correct multiplicative formula in the source's normalization.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tameValue_symbol (d : DiscreteResidueData K k) (a b : Kˣ) :
    tameValue d (symbol a b) =
      (-1 : kˣ) ^ (d.value (Additive.ofMul a) * d.value (Additive.ofMul b)) *
        (d.unitPart (Additive.ofMul a)).toMul ^ d.value (Additive.ofMul b) /
        (d.unitPart (Additive.ofMul b)).toMul ^ d.value (Additive.ofMul a) := rfl

/-- A symbol of two valuation units has zero additive tame value.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tame_units (d : DiscreteResidueData K k) (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    tame d (symbol u v) = 0 := by simp [tame_symbol, rawTame, hu, hv]

/-- The source convention `∂{u,π}=ū`, expressed additively in residue units.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tame_unit_uniformizer (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol u d.uniformizer) = d.unitPart (Additive.ofMul u) := by
  simp [tame_symbol, rawTame, hu, d.value_uniformizer]

/-- The convention `∂{u,π}=ū` in multiplicative residue notation.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tameValue_unit_uniformizer (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tameValue d (symbol u d.uniformizer) = (d.unitPart (Additive.ofMul u)).toMul := by
  exact congrArg Additive.toMul (tame_unit_uniformizer d u hu)

/-- Reversing the entries gives the inverse residue unit, by the proved skew symmetry.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tame_uniformizer_unit (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol d.uniformizer u) = -d.unitPart (Additive.ofMul u) := by
  rw [symbol_skew, map_neg, tame_unit_uniformizer d u hu]

/-- A field of characteristic `p` has no nontrivial `p`-power root of unity.
Source: the last assertion of `K2-018#lem:k2018-residue-bockstein`, proved here
using the characteristic-power identity rather than supplied as a premise.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem residueUnit_primePower_eq_one (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ) (u : kˣ) (hu : u ^ (p ^ r) = 1) : u = 1 := by
  apply Units.ext
  have hpow : (u : k) ^ (p ^ r) = 1 := by
    exact congrArg Units.val hu
  have hzero : ((u : k) - 1) ^ (p ^ r) = 0 := by
    rw [sub_pow_char_pow, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp hzero).1

/-- Residue-characteristic-primary torsion has tame value one.
Source: the last assertion of `K2-018#lem:k2018-residue-bockstein`; the constructed
tame homomorphism and the preceding field argument prove this conditional DVR statement.
Source: `K2-018#lem:k2018-residue-bockstein`, at the module snapshot
documented above. -/
theorem tameValue_primePower_torsion (d : DiscreteResidueData K k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (x : Group K)
    (hx : (p ^ r) • x = 0) : tameValue d x = 1 := by
  apply residueUnit_primePower_eq_one p r
  have ht : (p ^ r) • tame d x = 0 := by rw [← map_nsmul, hx, map_zero]
  exact congrArg Additive.toMul ht

end MilnorK.K2
