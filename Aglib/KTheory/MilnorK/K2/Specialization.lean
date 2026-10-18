/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.Residue
public import Aglib.KTheory.MilnorK.K2.Map

/-!
# Canonical specialization on the Milnor tame kernel

The residue unit parts define a specialization on full Milnor K₂ after an
elementary zero-valuation reduction law is supplied. This full-group map
uses the chosen uniformizer. If its residue unit parts change by
`r′(a)=r(a)−v(a) ε`, then
`s′(x)=s(x)−{∂x,ε}`. Skew symmetry gives the equivalent convention
`s′(x)−s(x)={ε,∂x}`. The correction vanishes on the actual kernel of the
constructed tame map, proving that the restriction is canonical under this
unit-part-change relation.

## Source correspondence

Source file: `research/exposes/K2/018/expose.tex`,
`K2-018#sec:k2018-splitting`, lines 240–249, together with the DVR convention
in `K2-018#lem:k2018-residue-bockstein`, lines 323–332, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This snapshot applies to every declaration below. The change and bilinear
identities are auxiliary algebraic foundations for the source specialization,
not additional assertions attributed verbatim to the manuscript.

Formalized scope: descent, the uniformizer-change identity, tame invariance,
canonical restriction to the actual Milnor tame kernel, and the constant
retraction/injectivity consequences. The explicit background consists of
`DiscreteResidueData`, the zero-valuation reduction law, and the specified
unit-part-change relation. For constants it additionally specifies their
valuation and residue unit parts. No specialization or injectivity theorem
is supplied as an input. Concrete DVR construction and the Matsumoto/Quillen
comparison remain separate background realizations. The map targets `K2 k`;
no assertion that integral generic classes specialize into `B₂(F)` is made.

## Implementation provenance

Original R5 implementation:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/Specialization.lean
Original Git blob SHA-1: `be5a8039ea5680958df9dcdad03708dc47375cfb`.
Original SHA-256: `af983c26e1abf33e7d04a8a1e80f83365f0025a2aea6d2bd6e1047d13cd12763`.
-/

@[expose] public section

namespace MilnorK.K2

variable {K k : Type*} [Field K] [Field k]

/-- Elementary DVR reduction of `a+b=1` when both entries have valuation zero.
Source: auxiliary DVR background for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
def UnitReductionCompatible (d : DiscreteResidueData K k) : Prop :=
  ∀ a b : Kˣ, (a : K) + (b : K) = 1 →
    d.value (Additive.ofMul a) = 0 → d.value (Additive.ofMul b) = 0 →
    ((d.unitPart (Additive.ofMul a)).toMul : k) +
      ((d.unitPart (Additive.ofMul b)).toMul : k) = 1

/-- The residue-unit-part symbol pairing before proving its Steinberg relation.
Source: auxiliary algebra for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
def specializationBilinear (d : DiscreteResidueData K k) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] Group k :=
  (symbolBilinear k).compl₁₂ d.unitPart d.unitPart

/-- The residue-unit-part pairing kills Steinberg tensors by all valuation cases.
Source: auxiliary specialization descent for `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
theorem specialization_steinberg (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b : Kˣ) (hab : (a : K) + (b : K) = 1) :
    specializationBilinear d (Additive.ofMul a) (Additive.ofMul b) = 0 := by
  change symbol (d.unitPart (Additive.ofMul a)).toMul
    (d.unitPart (Additive.ofMul b)).toMul = 0
  rcases lt_trichotomy (d.value (Additive.ofMul a)) 0 with hneg | hzero | hpos
  · obtain ⟨_, hub⟩ := d.negative a b hab hneg
    rw [hub]
    change symbol (d.unitPart (Additive.ofMul a)).toMul
      ((d.unitPart (Additive.ofMul a)).toMul * (-1)) = 0
    simpa using symbol_self_neg (d.unitPart (Additive.ofMul a)).toMul
  · rcases lt_trichotomy (d.value (Additive.ofMul b)) 0 with hbneg | hbzero | hbpos
    · obtain ⟨hva, _⟩ := d.negative b a (by simpa [add_comm] using hab) hbneg
      have hvb : d.value (Additive.ofMul b) = 0 := hva.symm.trans hzero
      exact steinberg _ _ (hd a b hab hzero hvb)
    · exact steinberg _ _ (hd a b hab hzero hbzero)
    · obtain ⟨_, hua⟩ := d.positive b a (by simpa [add_comm] using hab) hbpos
      rw [hua]
      exact symbol_one_left _
  · obtain ⟨_, hub⟩ := d.positive a b hab hpos
    rw [hub]
    exact symbol_one_right _

/-- Specialization on full Milnor K₂; its uniformizer dependence is computed below.
Source: auxiliary field specialization for `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
def specialize (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d) :
    Group K →ₗ[ℤ] Group k :=
  lift (specializationBilinear d) (fun a b hab => specialization_steinberg d hd a b hab)

/-- Specialization evaluates to the symbol of the two residue unit parts.
Source: auxiliary field specialization for `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
@[simp] theorem specialize_symbol (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (a b : Kˣ) :
    specialize d hd (symbol a b) =
      symbol (d.unitPart (Additive.ofMul a)).toMul (d.unitPart (Additive.ofMul b)).toMul := rfl

/-- The proved Milnor skew identity in additive unit notation.
Source: auxiliary symbol algebra for `K2-018#lem:k2018-residue-bockstein`,
at the module snapshot. -/
theorem bilinear_symbol_skew (u v : UnitsAdd k) :
    symbolBilinear k u v = -symbolBilinear k v u := symbol_skew u.toMul v.toMul

/-- The proved Milnor diagonal identity in additive unit notation.
Source: auxiliary symbol algebra for `K2-018#lem:k2018-residue-bockstein`,
at the module snapshot. -/
theorem bilinear_symbol_self (u : UnitsAdd k) :
    symbolBilinear k u u = symbolBilinear k u (residueSign k) := symbol_self u.toMul

/-- The bilinear expansion producing the sign-correct specialization correction.
Source: auxiliary algebra for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
theorem bilinear_symbol_change (u v e : UnitsAdd k) (m n : ℤ) :
    symbolBilinear k (u - m • e) (v - n • e) =
      symbolBilinear k u v -
        symbolBilinear k ((m * n) • residueSign k + n • u - m • v) e := by
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  rw [bilinear_symbol_skew e v, bilinear_symbol_self e,
    bilinear_symbol_skew e (residueSign k)]
  simp only [zsmul_sub, zsmul_neg, ← mul_zsmul]
  rw [mul_comm n m]
  abel

/-- The linear map `z↦{z,ε}` in the specialization-change identity.
Source: auxiliary algebra for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
def residueCorrection (e : UnitsAdd k) : UnitsAdd k →ₗ[ℤ] Group k :=
  (symbolBilinear k).flip e

/-- Changing residue unit parts by `r′=r−vε` preserves the constructed tame map.
Source: auxiliary invariance for `K2-018#lem:k2018-residue-bockstein`,
at the module snapshot. -/
theorem tame_eq_of_unitPart_change (d d' : DiscreteResidueData K k) (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) : tame d' = tame d := by
  apply linearMap_ext
  intro a b
  change rawTame d' (Additive.ofMul a) (Additive.ofMul b) =
    rawTame d (Additive.ofMul a) (Additive.ofMul b)
  simp only [rawTame, hvalue, hunit, zsmul_sub, ← mul_zsmul]
  rw [mul_comm (d.value (Additive.ofMul b)) (d.value (Additive.ofMul a))]
  abel

/-- Tame invariance identifies the actual kernels for two compatible decompositions.
Source: auxiliary canonicalization for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
theorem tame_kernel_eq_of_unitPart_change (d d' : DiscreteResidueData K k) (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    (tame d').ker = (tame d).ker :=
  congrArg (fun f : Group K →ₗ[ℤ] UnitsAdd k => f.ker)
    (tame_eq_of_unitPart_change d d' e hvalue hunit)

/-- The change formula `s′=s−{∂(-),ε}`, derived from symbols by the universal property.
Source: auxiliary canonicalization for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
theorem specialize_change (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    specialize d' hd' = specialize d hd - (residueCorrection e).comp (tame d) := by
  apply linearMap_ext
  intro a b
  change symbolBilinear k (d'.unitPart (Additive.ofMul a)) (d'.unitPart (Additive.ofMul b)) =
    symbolBilinear k (d.unitPart (Additive.ofMul a)) (d.unitPart (Additive.ofMul b)) -
      symbolBilinear k (rawTame d (Additive.ofMul a) (Additive.ofMul b)) e
  rw [hunit, hunit]
  exact bilinear_symbol_change _ _ _ _ _

/-- Skew symmetry rewrites the change formula as `s′(x)−s(x)={ε,∂x}`.
Source: auxiliary canonicalization for `K2-018#sec:k2018-splitting`, at the module snapshot. -/
theorem specialize_change_source_convention (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) (x : Group K) :
    specialize d' hd' x - specialize d hd x = symbolBilinear k e (tame d x) := by
  have h := LinearMap.congr_fun (specialize_change d d' hd hd' e hunit) x
  change specialize d' hd' x = specialize d hd x - symbolBilinear k (tame d x) e at h
  rw [h, bilinear_symbol_skew (tame d x) e]
  abel

/-- Specialization restricted to the actual kernel of the constructed tame homomorphism.
Source: the field-specialization part of `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
def unramifiedSpecialize (d : DiscreteResidueData K k) (hd : UnitReductionCompatible d) :
    (tame d).ker →ₗ[ℤ] Group k := (specialize d hd).comp (tame d).ker.subtype

/-- The specialization correction vanishes on the actual tame kernel.
Together with tame invariance, this proves uniformizer independence under the
explicit unit-part-change background relation.
Source: auxiliary proof of canonical field specialization for `K2-018#sec:k2018-splitting`,
at the module snapshot; no arithmetic `B₂(F)` landing is asserted. -/
theorem specialize_eq_on_tame_kernel (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    (specialize d' hd').comp (tame d).ker.subtype = unramifiedSpecialize d hd := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (specialize_change d d' hd hd' e hunit) (x : Group K)
  change specialize d' hd' x = specialize d hd x - residueCorrection e (tame d x) at h
  have hx : tame d x = 0 := x.property
  simpa [unramifiedSpecialize, hx] using h

/-- Constants of valuation zero lie in the actual tame kernel.
Source: auxiliary origin-constant algebra for `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
theorem tame_map_constants (d : DiscreteResidueData K k) (i : k →+* K)
    (hvalue : ∀ a : kˣ, d.value (unitsLinear i (Additive.ofMul a)) = 0) :
    (tame d).comp (map i) = 0 := by
  apply linearMap_ext
  intro a b
  change rawTame d (unitsLinear i (Additive.ofMul a)) (unitsLinear i (Additive.ofMul b)) = 0
  simp [rawTame, hvalue]

/-- Residue unit parts agreeing with constants give a specialization retraction.
Source: the field-constant section identity behind `K2-018#sec:k2018-splitting`,
at the module snapshot; the residue compatibility is an explicit elementary input. -/
theorem specialize_map_constants (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    (specialize d hd).comp (map i) = LinearMap.id := by
  apply linearMap_ext
  intro a b
  change symbol (d.unitPart (unitsLinear i (Additive.ofMul a))).toMul
    (d.unitPart (unitsLinear i (Additive.ofMul b))).toMul = symbol a b
  rw [hunit, hunit]
  rfl

/-- The Milnor constant map is injective because specialization is its left inverse.
Source: auxiliary derivation of constant injectivity for `K2-018#sec:k2018-splitting`,
at the module snapshot; injectivity is a conclusion, never a premise. -/
theorem map_constants_injective (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    Function.Injective (map i) :=
  (show Function.LeftInverse (specialize d hd) (map i) from
    fun x => LinearMap.congr_fun (specialize_map_constants d hd i hunit) x).injective

/-- The constant map with codomain the actual tame kernel, by the zero-valuation theorem.
Source: auxiliary origin-constant algebra for `K2-018#sec:k2018-splitting`,
at the module snapshot. -/
def unramifiedConstants (d : DiscreteResidueData K k) (i : k →+* K)
    (hvalue : ∀ a : kˣ, d.value (unitsLinear i (Additive.ofMul a)) = 0) :
    Group k →ₗ[ℤ] (tame d).ker :=
  (map i).codRestrict (tame d).ker (fun x =>
    LinearMap.congr_fun (tame_map_constants d i hvalue) x)

/-- Canonical field specialization retracts constants in the actual unramified kernel.
Source: the field part of `K2-018#sec:k2018-splitting`, at the module snapshot.
The separate integral-image-to-`B₂(F)` condition remains unformalized here. -/
theorem unramified_constants_retraction (d : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (i : k →+* K)
    (hvalue : ∀ a : kˣ, d.value (unitsLinear i (Additive.ofMul a)) = 0)
    (hunit : ∀ a : kˣ, d.unitPart (unitsLinear i (Additive.ofMul a)) = Additive.ofMul a) :
    (unramifiedSpecialize d hd).comp (unramifiedConstants d i hvalue) = LinearMap.id := by
  exact specialize_map_constants d hd i hunit

end MilnorK.K2
