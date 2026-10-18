/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.Specialization

/-!
# An actual degree-three Milnor residue

`K3 K` is the quotient of `UnitsAdd K ⊗[ℤ] K2 K` by the first-adjacent
Steinberg relations. The last-adjacent relations already hold in the original
Milnor `K2 K` tensor quotient. The explicit sign-correct bilinear precursor
is proved cyclic and therefore descends to this quotient.

The valuation/reduction hypotheses are exactly `DiscreteResidueData` and
`UnitReductionCompatible`. This is an algebraic residue construction; it
neither realizes those hypotheses for DVRs nor constructs a finite-extension
norm, reciprocity theorem, or motivic comparison. The original degree-two
tame convention puts the uniformizer last. In degree three, moving it between
the first and last positions has positive sign.
-/

@[expose] public section

namespace MilnorK.K3

open MilnorK.K2

variable (K : Type*) [Field K]

/-- The nested tensor presentation before first-adjacent Steinberg descent. -/
abbrev T3 := TensorProduct ℤ (UnitsAdd K) (MilnorK.K2.Group K)

/-- First-adjacent Steinberg tensors; the last pair already lies in actual Milnor K₂. -/
def steinbergGenerators : Set (T3 K) :=
  {t | ∃ a b c : Kˣ, (a : K) + (b : K) = 1 ∧
    t = TensorProduct.tmul ℤ (Additive.ofMul a) (symbol b c)}

/-- The integer span of the first-adjacent Steinberg relations. -/
def R3 : Submodule ℤ (T3 K) := Submodule.span ℤ (steinbergGenerators K)

/-- Milnor K₃ in the nested tensor/Steinberg presentation. -/
abbrev Group := T3 K ⧸ R3 K

variable {K}

/-- A degree-three unit symbol in the actual nested quotient. -/
def symbol3 (a b c : Kˣ) : Group K :=
  (R3 K).mkQ (TensorProduct.tmul ℤ (Additive.ofMul a) (symbol b c))

/-- The quotient symbol is multiplicatively additive in its first entry. -/
theorem symbol3_mul_left (a a' b c : Kˣ) :
    symbol3 (a * a') b c = symbol3 a b c + symbol3 a' b c := by
  change (R3 K).mkQ
    (TensorProduct.tmul ℤ (Additive.ofMul a + Additive.ofMul a') (symbol b c)) = _
  rw [TensorProduct.add_tmul, map_add]
  rfl

/-- The quotient symbol is multiplicatively additive in its middle entry. -/
theorem symbol3_mul_middle (a b b' c : Kˣ) :
    symbol3 a (b * b') c = symbol3 a b c + symbol3 a b' c := by
  simp only [symbol3, symbol_mul_left, TensorProduct.tmul_add, map_add]

/-- The quotient symbol is multiplicatively additive in its last entry. -/
theorem symbol3_mul_right (a b c c' : Kˣ) :
    symbol3 a b (c * c') = symbol3 a b c + symbol3 a b c' := by
  simp only [symbol3, symbol_mul_right, TensorProduct.tmul_add, map_add]

/-- The first-adjacent Steinberg relation holds by the defining span. -/
theorem symbol3_steinberg_left (a b c : Kˣ) (hab : (a : K) + (b : K) = 1) :
    symbol3 a b c = 0 := by
  change (Submodule.Quotient.mk
    (TensorProduct.tmul ℤ (Additive.ofMul a) (symbol b c)) : Group K) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨a, b, c, hab, rfl⟩

/-- The last-adjacent Steinberg relation is inherited from actual Milnor K₂. -/
theorem symbol3_steinberg_right (a b c : Kˣ) (hbc : (b : K) + (c : K) = 1) :
    symbol3 a b c = 0 := by
  simp [symbol3, steinberg b c hbc]

variable {A : Type*} [AddCommGroup A]

/-- A bilinear function on units and actual K₂ killing the first relation descends. -/
def lift (b : UnitsAdd K →ₗ[ℤ] MilnorK.K2.Group K →ₗ[ℤ] A)
    (hb : ∀ a c e : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (symbol c e) = 0) : Group K →ₗ[ℤ] A :=
  (R3 K).liftQ (TensorProduct.lift b) (by
    rw [R3, Submodule.span_le]
    rintro t ⟨a, c, e, hac, rfl⟩
    exact hb a c e hac)

/-- The quotient lift takes the prescribed values on actual symbols. -/
@[simp] theorem lift_symbol3 (b : UnitsAdd K →ₗ[ℤ] MilnorK.K2.Group K →ₗ[ℤ] A)
    (hb : ∀ a c e : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (symbol c e) = 0) (a c e : Kˣ) :
    lift b hb (symbol3 a c e) = b (Additive.ofMul a) (symbol c e) := rfl

variable {k : Type*} [Field k]

/-- Pairing the residue sign with any entry gives a two-torsion K₂ class. -/
theorem bilinear_residueSign_neg (u : UnitsAdd k) :
    -symbolBilinear k (residueSign k) u = symbolBilinear k (residueSign k) u := by
  have h := congrArg (fun a : UnitsAdd k => symbolBilinear k a u)
    (residueSign_add_self (k := k))
  simp only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply] at h
  exact (eq_neg_of_add_eq_zero_left h).symm

/-- The sign pairing is symmetric because skew symmetry and two-torsion agree. -/
theorem bilinear_residueSign_swap (u : UnitsAdd k) :
    symbolBilinear k u (residueSign k) = symbolBilinear k (residueSign k) u := by
  rw [bilinear_symbol_skew, bilinear_residueSign_neg]

/-- Integer multiples of the sign pairing are also fixed by negation. -/
theorem bilinear_residueSign_zsmul_neg (u : UnitsAdd k) (m : ℤ) :
    -(m • symbolBilinear k (residueSign k) u) =
      m • symbolBilinear k (residueSign k) u := by
  rw [← smul_neg, bilinear_residueSign_neg]

/-- The complete sign-correct expansion into a manifestly cyclic seven-term sum. -/
theorem bilinear_residue_cyclic_expansion (u v w : UnitsAdd k) (m n l : ℤ) :
    m • symbolBilinear k v w +
        symbolBilinear k (u - m • residueSign k)
          ((n * l) • residueSign k + l • v - n • w) =
      m • symbolBilinear k v w + n • symbolBilinear k w u + l • symbolBilinear k u v +
        (m * n) • symbolBilinear k (residueSign k) w +
        (n * l) • symbolBilinear k (residueSign k) u +
        (l * m) • symbolBilinear k (residueSign k) v +
        (m * n * l) • symbolBilinear k (residueSign k) (residueSign k) := by
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [bilinear_residueSign_swap u, bilinear_symbol_skew u w]
  simp only [zsmul_sub, zsmul_neg, ← mul_zsmul]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg, bilinear_residueSign_zsmul_neg]
  simp only [mul_comm, mul_left_comm]
  abel

/-- The explicit residue precursor is bilinear, including the necessary sign correction. -/
def residue3Bilinear (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d) :
    UnitsAdd K →ₗ[ℤ] MilnorK.K2.Group K →ₗ[ℤ] MilnorK.K2.Group k :=
  d.value.smulRight (specialize d hd) +
    (symbolBilinear k).compl₁₂
      (d.unitPart - d.value.smulRight (residueSign k)) (tame d)

/-- Evaluation of the bilinear precursor on any actual K₂ class. -/
@[simp] theorem residue3Bilinear_apply (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a : UnitsAdd K) (x : MilnorK.K2.Group K) :
    residue3Bilinear d hd a x = d.value a • specialize d hd x +
      symbolBilinear k (d.unitPart a - d.value a • residueSign k) (tame d x) := rfl

/-- The precursor's literal symbol formula in terms of the two existing residue maps. -/
theorem residue3Bilinear_symbol (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b c : Kˣ) :
    residue3Bilinear d hd (Additive.ofMul a) (symbol b c) =
      d.value (Additive.ofMul a) •
          symbolBilinear k (d.unitPart (Additive.ofMul b)) (d.unitPart (Additive.ofMul c)) +
        symbolBilinear k
          (d.unitPart (Additive.ofMul a) - d.value (Additive.ofMul a) • residueSign k)
          (rawTame d (Additive.ofMul b) (Additive.ofMul c)) := rfl

/-- Cyclicity follows from the full expansion, including all residue-sign terms. -/
theorem residue3Bilinear_cyclic (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b c : Kˣ) :
    residue3Bilinear d hd (Additive.ofMul a) (symbol b c) =
      residue3Bilinear d hd (Additive.ofMul c) (symbol a b) := by
  simp only [residue3Bilinear_symbol, rawTame, bilinear_residue_cyclic_expansion]
  simp only [mul_comm, mul_left_comm]
  abel

/-- Cyclicity moves the first Steinberg pair into the already constructed K₂ argument. -/
theorem residue3Bilinear_steinberg (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b c : Kˣ) (hab : (a : K) + (b : K) = 1) :
    residue3Bilinear d hd (Additive.ofMul a) (symbol b c) = 0 := by
  rw [residue3Bilinear_cyclic d hd a b c, steinberg a b hab, map_zero]

/-- The actual degree-three residue, descended through the nested Milnor quotient. -/
def residue3 (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d) :
    Group K →ₗ[ℤ] MilnorK.K2.Group k :=
  lift (residue3Bilinear d hd) (fun a b c hab => residue3Bilinear_steinberg d hd a b c hab)

/-- The descended residue agrees with its explicit precursor on every symbol. -/
@[simp] theorem residue3_symbol (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b c : Kˣ) :
    residue3 d hd (symbol3 a b c) =
      residue3Bilinear d hd (Additive.ofMul a) (symbol b c) := rfl

/-- The residue of three valuation units vanishes. -/
theorem residue3_units (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d)
    (a b c : Kˣ) (ha : d.value (Additive.ofMul a) = 0)
    (hb : d.value (Additive.ofMul b) = 0) (hc : d.value (Additive.ofMul c) = 0) :
    residue3 d hd (symbol3 a b c) = 0 := by
  rw [residue3_symbol, residue3Bilinear_apply, ha, tame_units d b c hb hc]
  simp

/-- The first-slot uniformizer normalization is the literal symbol of reduced units. -/
theorem residue3_uniformizer_units (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    residue3 d hd (symbol3 d.uniformizer u v) =
      symbol (d.unitPart (Additive.ofMul u)).toMul (d.unitPart (Additive.ofMul v)).toMul := by
  rw [residue3_symbol, residue3Bilinear_apply, tame_units d u v hu hv]
  simp only [d.value_uniformizer, one_smul, map_zero, add_zero, specialize_symbol]

/-- The constructed residue is cyclic on unit symbols. -/
theorem residue3_cyclic (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b c : Kˣ) :
    residue3 d hd (symbol3 a b c) = residue3 d hd (symbol3 c a b) :=
  residue3Bilinear_cyclic d hd a b c

/-- Sign regression: two uniformizers produce the sign-unit symbol, not a forced zero. -/
theorem residue3_uniformizer_uniformizer_unit (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (u : Kˣ) (hu : d.value (Additive.ofMul u) = 0) :
    residue3 d hd (symbol3 d.uniformizer d.uniformizer u) =
      symbolBilinear k (residueSign k) (d.unitPart (Additive.ofMul u)) := by
  rw [residue3_symbol, residue3Bilinear_apply, tame_uniformizer_unit d u hu]
  change d.value (Additive.ofMul d.uniformizer) •
      symbolBilinear k (d.unitPart (Additive.ofMul d.uniformizer)) (d.unitPart (Additive.ofMul u)) +
    symbolBilinear k (d.unitPart (Additive.ofMul d.uniformizer) -
      d.value (Additive.ofMul d.uniformizer) • residueSign k)
      (-d.unitPart (Additive.ofMul u)) = _
  simp [d.value_uniformizer, d.unitPart_uniformizer]

/-- Three uniformizers retain the negative sign pairing in the literal formula. -/
theorem residue3_uniformizer_three (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) :
    residue3 d hd (symbol3 d.uniformizer d.uniformizer d.uniformizer) =
      -symbolBilinear k (residueSign k) (residueSign k) := by
  rw [residue3_symbol, residue3Bilinear_symbol]
  simp [rawTame, d.value_uniformizer, d.unitPart_uniformizer]

/-- The three-uniformizer answer also equals the positive pairing, by two-torsion. -/
theorem residue3_uniformizer_three_sign (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) :
    residue3 d hd (symbol3 d.uniformizer d.uniformizer d.uniformizer) =
      symbolBilinear k (residueSign k) (residueSign k) := by
  rw [residue3_uniformizer_three, bilinear_residueSign_neg]

end MilnorK.K3
