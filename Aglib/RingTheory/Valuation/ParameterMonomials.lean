/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Valuation.IntegerMap
public import Aglib.RingTheory.Valuation.LeadingRelation
public import Aglib.RingTheory.MvPolynomial.ResidueFrobenius
public import Aglib.LinearAlgebra.LinearIndependent.FiniteBasisChange
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Valuative independence of parameter monomials
-/

@[expose] public noncomputable section

open scoped BigOperators
open WithZero

namespace Valuation

variable {K L σ : Type*} [Field K] [Field L]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰)

/-- Normalized orthogonal coefficients times bounded parameter monomials are
Frobenius-independent. The two residue squares are literal scalar/variable
identities for the supplied maps. The target residue field is an actual
fraction ring, not merely an abstract field with enough independent elements. -/
theorem IsOrthogonal.linearIndependent_parameterMonomials
    {ι ρ : Type*} [Fintype ι] [Finite ρ]
    (p : ℕ) (hp : 0 < p) [ExpChar K p] [ExpChar L p]
    [ExpChar (IsLocalRing.ResidueField v.valuationSubring) p]
    [ExpChar (IsLocalRing.ResidueField w.valuationSubring) p]
    [Algebra (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
      (IsLocalRing.ResidueField w.valuationSubring)]
    [IsFractionRing (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
      (IsLocalRing.ResidueField w.valuationSubring)]
    (f : K →+* L) (hf : ∀ x, w (f x) = v x)
    (π : K) (hπ : v π = exp (-1))
    (z : σ → w.valuationSubring) (hz : ∀ x, w (z x : L) = 1)
    (hcoeff : ∀ x : v.valuationSubring,
      IsLocalRing.residue w.valuationSubring (v.integerMap w f hf x) =
        algebraMap (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
          (IsLocalRing.ResidueField w.valuationSubring)
          (MvPolynomial.C (IsLocalRing.residue v.valuationSubring x)))
    (hvar : ∀ x, IsLocalRing.residue w.valuationSubring (z x) =
      algebraMap (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
        (IsLocalRing.ResidueField w.valuationSubring) (MvPolynomial.X x))
    {b : ι → K} (hb : v.IsOrthogonal (frobenius K p).fieldRange b)
    (r : ι → ℤ) (hr0 : ∀ i, 0 ≤ r i) (hrp : ∀ i, r i < p)
    (hbval : ∀ i, v (b i) = exp (-r i))
    (e : ρ → σ →₀ ℕ) (he : ∀ i x, e i x < p) (heinj : Function.Injective e) :
    LinearIndependent (frobenius L p).fieldRange
      (fun q : ρ × ι => (MvPolynomial.eval₂Hom f (fun x => (z x : L)))
        (MvPolynomial.monomial (e q.1) (b q.2))) := by
  classical
  let := Fintype.ofFinite ρ
  let A := v.valuationSubring
  let B := w.valuationSubring
  let k := IsLocalRing.ResidueField A
  let l := IsLocalRing.ResidueField B
  let Z (a : ρ) : B := (e a).prod (fun x n => z x ^ n)
  have hZ (a : ρ) : w (Z a : L) = 1 := by
    simp only [Z, Finsupp.prod, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow,
      map_prod, map_pow, hz, one_pow, Finset.prod_const_one]
  let b' (q : ρ × ι) : L := f (b q.2) * (Z q.1 : L)
  have hb' (q : ρ × ι) : w (b' q) = exp (-r q.2) := by
    dsimp only [b']
    rw [map_mul, hf, hbval, hZ, mul_one]
  have hπ' : w (f π) = exp (-1) := by rw [hf, hπ]
  have hlead (s : ℤ) (q : {q : ρ × ι // r q.2 = s}) :
      w.leadingInteger (f π) hπ' s (b' q) (by simpa only [q.property] using hb' q) =
        v.integerMap w f hf
          (v.leadingInteger π hπ s (b q.val.2) (by simpa only [q.property] using hbval q.val.2)) *
        Z q.val.1 := by
    apply Subtype.ext
    change (f (b q.val.2) * (Z q.val.1 : L)) * (f π) ^ (-s) =
      f (b q.val.2 * π ^ (-s)) * (Z q.val.1 : L)
    rw [map_mul, map_zpow₀]
    ring
  have hres : ∀ s : ℤ,
      LinearIndependent (frobenius l p).fieldRange
        (fun q : {q : ρ × ι // r q.2 = s} => IsLocalRing.residue B
          (w.leadingInteger (f π) hπ' s (b' q)
            (by simpa only [q.property] using hb' q))) := by
    intro s
    let β (j : {i // r i = s}) : k := IsLocalRing.residue A
      (v.leadingInteger π hπ s (b j) (by simpa only [j.property] using hbval j))
    have hβ : LinearIndependent (frobenius k p).fieldRange β :=
      Valuation.IsOrthogonal.linearIndependent_leadingResidues v p π hπ hb r hbval s
    have H := MvPolynomial.linearIndependent_monomial_fractionRing_frobeniusFieldRange
      (G := l) p (Nat.ne_of_gt hp) hβ e he heinj
    let E : {q : ρ × ι // r q.2 = s} ≃ ρ × {i // r i = s} :=
      { toFun := fun q => (q.val.1, ⟨q.val.2, q.property⟩)
        invFun := fun q => ⟨(q.1, q.2.val), q.2.property⟩
        left_inv := fun q => by cases q; rfl
        right_inv := fun q => by cases q; rfl }
    have HH := H.comp E E.injective
    convert HH using 1
    ext q
    change _ = algebraMap (MvPolynomial σ k) l
      (MvPolynomial.monomial (e q.val.1) (β ⟨q.val.2, q.property⟩))
    rw [hlead, map_mul, hcoeff, MvPolynomial.monomial_eq, map_mul]
    congr 1
    simp only [Z, Finsupp.prod, map_prod, map_pow]
    apply Finset.prod_congr rfl
    intro x hx
    exact congrArg (fun a => a ^ (e q.val.1) x) (hvar x)
  have H := w.linearIndependent_frobenius_of_leadingResidues p hp (f π) hπ'
    b' (fun q => r q.2) (fun q => hr0 q.2) (fun q => hrp q.2) hb' hres
  convert H using 1
  ext q
  simp only [MvPolynomial.eval₂Hom_monomial, b', Z, Finsupp.prod,
    SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow]

/-- Arbitrary finite independent coefficient families reduce to a normalized
orthogonal basis of their finite span. Completeness is used only to obtain that
finite basis. All fraction-field and residue actions remain the supplied ones. -/
theorem linearIndependent_parameterMonomials
    {ι ρ : Type*} [Finite ι] [Finite ρ]
    (p : ℕ) (hp : 0 < p) [ExpChar K p] [ExpChar L p]
    [ExpChar (IsLocalRing.ResidueField v.valuationSubring) p]
    [ExpChar (IsLocalRing.ResidueField w.valuationSubring) p]
    [Algebra (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
      (IsLocalRing.ResidueField w.valuationSubring)]
    [IsFractionRing (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
      (IsLocalRing.ResidueField w.valuationSubring)]
    (hK : v.IsSeqComplete)
    (f : K →+* L) (hf : ∀ x, w (f x) = v x)
    (π : K) (hπ : v π = exp (-1))
    (z : σ → w.valuationSubring) (hz : ∀ x, w (z x : L) = 1)
    (hcoeff : ∀ x : v.valuationSubring,
      IsLocalRing.residue w.valuationSubring (v.integerMap w f hf x) =
        algebraMap (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
          (IsLocalRing.ResidueField w.valuationSubring)
          (MvPolynomial.C (IsLocalRing.residue v.valuationSubring x)))
    (hvar : ∀ x, IsLocalRing.residue w.valuationSubring (z x) =
      algebraMap (MvPolynomial σ (IsLocalRing.ResidueField v.valuationSubring))
        (IsLocalRing.ResidueField w.valuationSubring) (MvPolynomial.X x))
    {a : ι → K} (ha : LinearIndependent (frobenius K p).fieldRange a)
    (e : ρ → σ →₀ ℕ) (he : ∀ i x, e i x < p) (heinj : Function.Injective e) :
    LinearIndependent (frobenius L p).fieldRange
      (fun q : ρ × ι => (MvPolynomial.eval₂Hom f (fun x => (z x : L)))
        (MvPolynomial.monomial (e q.1) (a q.2))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ρ
  let E := (frobenius K p).fieldRange
  let F := (frobenius L p).fieldRange
  let W := Submodule.span E (Set.range a)
  let : Module.Finite E W := Module.Finite.span_of_finite E (Set.finite_range a)
  obtain ⟨n, b, r, hbli, hspan, hborth, hbr⟩ :=
    v.exists_normalized_frobenius_orthogonal_span hK p hp π hπ W
  have H := Valuation.IsOrthogonal.linearIndependent_parameterMonomials v w p hp f hf π hπ z hz
    hcoeff hvar hborth r (fun i => (hbr i).1) (fun i => (hbr i).2.1)
      (fun i => (hbr i).2.2) e he heinj
  let τ : E →+* F :=
    { toFun := fun c => ⟨f c, by
        obtain ⟨x, hx⟩ := c.property
        exact ⟨f x, by simpa only [frobenius_def, map_pow] using congrArg f hx⟩⟩
      map_zero' := Subtype.ext (map_zero f)
      map_one' := Subtype.ext (map_one f)
      map_add' x y := Subtype.ext (map_add f (x : K) (y : K))
      map_mul' x y := Subtype.ext (map_mul f (x : K) (y : K)) }
  let Z (j : ρ) : L := (e j).prod (fun x n => (z x : L) ^ n)
  have HB : LinearIndependent F (fun q : ρ × Fin n => f (b q.2) * Z q.1) := by
    simpa only [MvPolynomial.eval₂Hom_monomial, Z] using H
  have HA := LinearIndependent.mul_of_span_eq E F f τ (fun c => rfl) ha hbli hspan.symm Z HB
  simpa only [MvPolynomial.eval₂Hom_monomial, Z] using HA

end Valuation
