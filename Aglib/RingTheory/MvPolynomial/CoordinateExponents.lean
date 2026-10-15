/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinateGrading
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Card

/-!
# Complementary polynomial and all-negative Laurent exponents

The literal complement `βᵢ = -1 - αᵢ` identifies natural polynomial exponents
with all-negative exponents in the native coordinate Laurent exponent monoid.
The degree-`d` all-negative exponents correspond to nonnegative exponents of
integer total degree `-d - card ι`; consequently they form a finite type and
are empty above degree `-card ι`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The actual Laurent exponent complementary to a polynomial exponent for
the residue at the all-minus-one monomial. -/
def coordinateNegativeComplement (a : ι →₀ ℕ) :
    coordinateExponentMonoid (Finset.univ : Finset ι) :=
  ⟨(coordinateNegativeProductExponent Finset.univ).val -
      (coordinateExponentOfNat Finset.univ a).val, by
    intro i hi
    simp at hi⟩

@[simp]
theorem coordinateNegativeComplement_apply (a : ι →₀ ℕ) (i : ι) :
    (coordinateNegativeComplement a).val i = -1 - (a i : ℤ) := by
  simp [coordinateNegativeComplement, coordinateNegativeProductExponent]

theorem coordinateNegativeComplement_neg (a : ι →₀ ℕ) (i : ι) :
    (coordinateNegativeComplement a).val i < 0 := by
  rw [coordinateNegativeComplement_apply]
  omega

/-- The native integer degree of the complementary Laurent monomial. -/
theorem coordinateNegativeComplement_degree (a : ι →₀ ℕ) :
    coordinateDegree Finset.univ (coordinateNegativeComplement a) =
      -(a.degree : ℤ) - (Fintype.card ι : ℤ) := by
  change Finsupp.degree ((coordinateNegativeProductExponent Finset.univ).val -
    (coordinateExponentOfNat Finset.univ a).val) = _
  rw [map_sub]
  change coordinateDegree Finset.univ (coordinateNegativeProductExponent Finset.univ) -
    coordinateDegree Finset.univ (coordinateExponentOfNat Finset.univ a) = _
  rw [coordinateDegree_negativeProduct, coordinateDegree_ofNat, Finset.card_univ]
  omega

/-- The natural exponent complementary to an all-negative native Laurent exponent. -/
def coordinateNonnegativeComplement
    (e : coordinateExponentMonoid (Finset.univ : Finset ι)) : ι →₀ ℕ :=
  ((coordinateNegativeProductExponent Finset.univ).val - e.val).mapRange Int.toNat (by rfl)

@[simp]
theorem coordinateNonnegativeComplement_apply
    (e : coordinateExponentMonoid (Finset.univ : Finset ι)) (i : ι) :
    coordinateNonnegativeComplement e i = (-1 - e.val i).toNat := by
  simp [coordinateNonnegativeComplement, coordinateNegativeProductExponent]

@[simp]
theorem coordinateNonnegativeComplement_negativeComplement (a : ι →₀ ℕ) :
    coordinateNonnegativeComplement (coordinateNegativeComplement a) = a := by
  ext i
  simp

theorem coordinateNegativeComplement_nonnegativeComplement
    (e : coordinateExponentMonoid (Finset.univ : Finset ι)) (he : ∀ i, e.val i < 0) :
    coordinateNegativeComplement (coordinateNonnegativeComplement e) = e := by
  apply Subtype.ext
  ext i
  rw [coordinateNegativeComplement_apply, coordinateNonnegativeComplement_apply,
    Int.toNat_of_nonneg (by have := he i; omega)]
  omega

/-- Literal exponent complementation, retaining the original coordinate exponent monoid. -/
def coordinateNegativeComplementEquiv :
    (ι →₀ ℕ) ≃ {e : coordinateExponentMonoid (Finset.univ : Finset ι) // ∀ i, e.val i < 0} where
  toFun a := ⟨coordinateNegativeComplement a, coordinateNegativeComplement_neg a⟩
  invFun e := coordinateNonnegativeComplement e.val
  left_inv := coordinateNonnegativeComplement_negativeComplement
  right_inv e := Subtype.ext (coordinateNegativeComplement_nonnegativeComplement e.val e.property)

/-- The actual all-negative monomial indices in a specified Laurent degree. -/
abbrev coordinateNegativeDegreeExponents (d : ℤ) :=
  {e : coordinateExponentMonoid (Finset.univ : Finset ι) //
    coordinateDegree Finset.univ e = d ∧ ∀ i, e.val i < 0}

/-- Complementation identifies every all-negative Laurent degree with the
corresponding native natural-exponent degree. The integer degree may be negative. -/
def coordinateNegativeDegreeExponentEquiv (d : ℤ) :
    {a : ι →₀ ℕ // (a.degree : ℤ) = -d - (Fintype.card ι : ℤ)} ≃
      coordinateNegativeDegreeExponents (ι := ι) d where
  toFun a := ⟨coordinateNegativeComplement a.val,
    ⟨by rw [coordinateNegativeComplement_degree]; have := a.property; omega,
      coordinateNegativeComplement_neg a.val⟩⟩
  invFun e := ⟨coordinateNonnegativeComplement e.val, by
    have h := congrArg (coordinateDegree Finset.univ)
      (coordinateNegativeComplement_nonnegativeComplement e.val e.property.2)
    rw [coordinateNegativeComplement_degree, e.property.1] at h
    omega⟩
  left_inv a := Subtype.ext (coordinateNonnegativeComplement_negativeComplement a.val)
  right_inv e := Subtype.ext (coordinateNegativeComplement_nonnegativeComplement e.val e.property.2)

omit [Fintype ι] in
/-- Fixed integer degree imposes a finite set of natural exponent vectors. -/
theorem finite_naturalExponents_of_int_degree [Finite ι] (d : ℤ) :
    {a : ι →₀ ℕ | (a.degree : ℤ) = d}.Finite := by
  apply (Finsupp.finite_of_degree_eq d.toNat).subset
  intro a ha
  simpa using congrArg Int.toNat ha

instance (d : ℤ) : Finite (coordinateNegativeDegreeExponents (ι := ι) d) := by
  have : Finite {a : ι →₀ ℕ // (a.degree : ℤ) = -d - (Fintype.card ι : ℤ)} :=
    (finite_naturalExponents_of_int_degree (ι := ι)
    (-d - (Fintype.card ι : ℤ))).to_subtype
  exact Finite.of_equiv _ (coordinateNegativeDegreeExponentEquiv d)

/-- There are no all-negative Laurent exponents above the residue degree. -/
theorem coordinateNegativeDegreeExponents_isEmpty (d : ℤ) (hd : -(Fintype.card ι : ℤ) < d) :
    IsEmpty (coordinateNegativeDegreeExponents (ι := ι) d) := by
  refine ⟨fun e => ?_⟩
  have h := ((coordinateNegativeDegreeExponentEquiv d).symm e).property
  have hnat : 0 ≤
      ((((coordinateNegativeDegreeExponentEquiv d).symm e).val.degree : ℕ) : ℤ) := by omega
  omega

omit [Fintype ι] in
/-- The native nonnegative integer-exponent vectors of the indicated degree. -/
abbrev coordinateNonnegativeDegreeExponents (d : ℤ) :=
  {e : ι →₀ ℤ // e.degree = d ∧ ∀ i, 0 ≤ e i}

omit [Fintype ι] in
/-- The original cast of natural monomial exponents identifies integer degree
with the native nonnegative integer-exponent fiber. -/
def coordinateNonnegativeDegreeExponentEquiv (d : ℤ) :
    {a : ι →₀ ℕ // (a.degree : ℤ) = d} ≃
      coordinateNonnegativeDegreeExponents (ι := ι) d where
  toFun a := ⟨(coordinateExponentOfNat ∅ a.val).val, ⟨by
    change coordinateDegree ∅ (coordinateExponentOfNat ∅ a.val) = d
    rw [coordinateDegree_ofNat, a.property], by
    intro i
    exact Int.natCast_nonneg _⟩⟩
  invFun e := ⟨e.val.mapRange Int.toNat (by rfl), by
    have he : (coordinateExponentOfNat ∅ (e.val.mapRange Int.toNat (by rfl))).val = e.val := by
      ext i
      change ((e.val i).toNat : ℤ) = e.val i
      exact Int.toNat_of_nonneg (e.property.2 i)
    rw [← coordinateDegree_ofNat (∅ : Finset ι)]
    change ((coordinateExponentOfNat ∅ (e.val.mapRange Int.toNat (by rfl))).val).degree = d
    rw [he, e.property.1]⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    change ((a.val i : ℤ).toNat) = a.val i
    simp
  right_inv e := by
    apply Subtype.ext
    ext i
    change ((e.val i).toNat : ℤ) = e.val i
    exact Int.toNat_of_nonneg (e.property.2 i)

omit [Fintype ι] in
instance [Finite ι] (d : ℤ) : Finite (coordinateNonnegativeDegreeExponents (ι := ι) d) := by
  have : Finite {a : ι →₀ ℕ // (a.degree : ℤ) = d} :=
    (finite_naturalExponents_of_int_degree (ι := ι) d).to_subtype
  exact Finite.of_equiv _ (coordinateNonnegativeDegreeExponentEquiv d)

omit [Fintype ι] in
/-- Negative degree contains no native nonnegative integer-exponent vector. -/
theorem coordinateNonnegativeDegreeExponents_isEmpty (d : ℤ) (hd : d < 0) :
    IsEmpty (coordinateNonnegativeDegreeExponents (ι := ι) d) := by
  refine ⟨fun e => ?_⟩
  have h := ((coordinateNonnegativeDegreeExponentEquiv d).symm e).property
  have hz : 0 ≤
      ((((coordinateNonnegativeDegreeExponentEquiv d).symm e).val.degree : ℕ) : ℤ) := by omega
  omega

end MvPolynomial
