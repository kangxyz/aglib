/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Laurent monomials on coordinate localizations

For a finite set `s` of variables, the additive exponent monoid consists of integer exponent
vectors which are nonnegative outside `s`. Its native additive monoid algebra gives the
monomial description of the localization away from the product of the variables in `s`.
The polynomial map is the canonical cast of nonnegative exponents, preserving coefficients.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {ι : Type*}

/-- Integer exponent vectors allowed to be negative only at the selected coordinates. -/
def coordinateExponentMonoid (s : Finset ι) : AddSubmonoid (ι →₀ ℤ) where
  carrier e := ∀ i, i ∉ s → 0 ≤ e i
  zero_mem' := by intro i hi; simp
  add_mem' he hf := by intro i hi; exact add_nonneg (he i hi) (hf i hi)

/-- The canonical inclusion of nonnegative polynomial exponents into the coordinate
exponent monoid. -/
def coordinateExponentOfNat (s : Finset ι) : (ι →₀ ℕ) →+ coordinateExponentMonoid s where
  toFun e := ⟨e.mapRange (fun n : ℕ => (n : ℤ)) (by rfl), by intro i hi; simp⟩
  map_zero' := by apply Subtype.ext; ext i; simp
  map_add' e f := by apply Subtype.ext; ext i; simp

@[simp]
theorem coordinateExponentOfNat_apply (s : Finset ι) (e : ι →₀ ℕ) (i : ι) :
    (coordinateExponentOfNat s e).val i = (e i : ℤ) := rfl

theorem coordinateExponentOfNat_injective (s : Finset ι) :
    Function.Injective (coordinateExponentOfNat s) := by
  intro e f h
  ext i
  have h' := congrArg (fun z : coordinateExponentMonoid s => z.val i) h
  change (e i : ℤ) = (f i : ℤ) at h'
  exact_mod_cast h'

/-- The nonnegative exponent vector of the product of a finite set of coordinates. -/
def coordinateProductExponent (s : Finset ι) : ι →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i 1

@[simp]
theorem coordinateProductExponent_apply_of_mem (s : Finset ι) (i : ι) (hi : i ∈ s) :
    coordinateProductExponent s i = 1 := by
  classical
  simp [coordinateProductExponent, Finsupp.single_apply, hi]

@[simp]
theorem coordinateProductExponent_apply_of_not_mem (s : Finset ι) (i : ι) (hi : i ∉ s) :
    coordinateProductExponent s i = 0 := by
  classical
  simp [coordinateProductExponent, Finsupp.single_apply, hi]

/-- Every allowed Laurent exponent becomes a polynomial exponent after adding a sufficiently
large multiple of the coordinate-product exponent. -/
theorem coordinateExponent_exists_shift (s : Finset ι) (e : coordinateExponentMonoid s) :
    ∃ (n : ℕ) (a : ι →₀ ℕ),
      coordinateExponentOfNat s a =
        e + n • coordinateExponentOfNat s (coordinateProductExponent s) := by
  classical
  let n := s.sup (fun i => (e.val i).natAbs)
  let w := e.val + n • (coordinateExponentOfNat s (coordinateProductExponent s)).val
  have hw (i : ι) : 0 ≤ w i := by
    by_cases hi : i ∈ s
    · have hn : (e.val i).natAbs ≤ n := Finset.le_sup (f := fun i => (e.val i).natAbs) hi
      have he : 0 ≤ e.val i + (n : ℤ) := by
        cases h : e.val i with
        | ofNat m => omega
        | negSucc m =>
          have hm : m + 1 ≤ n := by simpa [h] using hn
          omega
      simpa [w, hi] using he
    · simpa [w, hi] using e.property i hi
  refine ⟨n, w.mapRange Int.toNat (by rfl), ?_⟩
  apply Subtype.ext
  ext i
  change ((w i).toNat : ℤ) = w i
  exact Int.toNat_of_nonneg (hw i)

/-- The negative of the coordinate-product exponent is allowed on the same localization. -/
def coordinateNegativeProductExponent (s : Finset ι) : coordinateExponentMonoid s :=
  ⟨-(coordinateExponentOfNat s (coordinateProductExponent s)).val, by
    intro i hi
    simp [hi]⟩

@[simp]
theorem coordinateProductExponent_add_negative (s : Finset ι) :
    coordinateExponentOfNat s (coordinateProductExponent s) +
      coordinateNegativeProductExponent s = 0 := by
  apply Subtype.ext
  exact add_neg_cancel _

@[simp]
theorem coordinateNegativeProductExponent_add (s : Finset ι) :
    coordinateNegativeProductExponent s +
      coordinateExponentOfNat s (coordinateProductExponent s) = 0 := by
  rw [add_comm, coordinateProductExponent_add_negative]

variable (R : Type*) [CommRing R]

/-- The native additive monoid algebra of exponents allowed on a coordinate localization. -/
abbrev coordinateLaurentAlgebra (s : Finset ι) := AddMonoidAlgebra R (coordinateExponentMonoid s)

/-- The coefficient-preserving polynomial map induced by the canonical inclusion of exponents. -/
def toCoordinateLaurent (s : Finset ι) : MvPolynomial ι R →ₐ[R] coordinateLaurentAlgebra R s :=
  AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentOfNat s)

@[simp]
theorem toCoordinateLaurent_monomial (s : Finset ι) (e : ι →₀ ℕ) (r : R) :
    toCoordinateLaurent R s (monomial e r) =
      AddMonoidAlgebra.single (coordinateExponentOfNat s e) r :=
  AddMonoidAlgebra.mapDomain_single

/-- The canonical polynomial map remains injective over arbitrary commutative coefficient rings. -/
theorem toCoordinateLaurent_injective (s : Finset ι) :
    Function.Injective (toCoordinateLaurent R s) :=
  AddMonoidAlgebra.mapDomain_injective (coordinateExponentOfNat_injective s)

/-- The coordinate product is the monomial of its indicator exponent vector. -/
theorem coordinateProduct_eq_monomial (s : Finset ι) :
    (∏ i ∈ s, X i : MvPolynomial ι R) = monomial (coordinateProductExponent s) 1 := by
  classical
  simpa [coordinateProductExponent, X] using
    (monomial_sum_one (R := R) s (fun i => Finsupp.single i 1)).symm

/-- The coordinate-product image is the corresponding Laurent monomial. -/
theorem toCoordinateLaurent_coordinateProduct (s : Finset ι) :
    toCoordinateLaurent R s (∏ i ∈ s, X i) =
      AddMonoidAlgebra.single (coordinateExponentOfNat s (coordinateProductExponent s)) 1 := by
  rw [coordinateProduct_eq_monomial, toCoordinateLaurent_monomial]

/-- The coordinate product becomes an explicit unit in the native Laurent monoid algebra. -/
def coordinateProductUnit (s : Finset ι) : (coordinateLaurentAlgebra R s)ˣ where
  val := toCoordinateLaurent R s (∏ i ∈ s, X i)
  inv := AddMonoidAlgebra.single (coordinateNegativeProductExponent s) 1
  val_inv := by
    rw [toCoordinateLaurent_coordinateProduct, AddMonoidAlgebra.single_mul_single,
      coordinateProductExponent_add_negative, one_mul]
    rfl
  inv_val := by
    rw [toCoordinateLaurent_coordinateProduct, AddMonoidAlgebra.single_mul_single,
      coordinateNegativeProductExponent_add, one_mul]
    rfl

/-- Every finite Laurent sum has a common denominator which is a power of the coordinate product. -/
theorem coordinateLaurent_exists_denominator (s : Finset ι) (f : coordinateLaurentAlgebra R s) :
    ∃ (n : ℕ) (p : MvPolynomial ι R),
      toCoordinateLaurent R s p = f * toCoordinateLaurent R s (∏ i ∈ s, X i) ^ n := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨m, p, hp⟩ := hf
    obtain ⟨n, q, hq⟩ := hg
    refine ⟨m + n, p * (∏ i ∈ s, X i) ^ n + q * (∏ i ∈ s, X i) ^ m, ?_⟩
    simp only [map_add, map_mul, map_pow, hp, hq, pow_add]
    ring
  | single e r =>
    obtain ⟨n, a, ha⟩ := coordinateExponent_exists_shift s e
    refine ⟨n, monomial a r, ?_⟩
    rw [toCoordinateLaurent_monomial, toCoordinateLaurent_coordinateProduct,
      AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single, one_pow, mul_one, ha]

/-- The polynomial-algebra structure is induced by the canonical exponent-inclusion map. -/
instance coordinateLaurentPolynomialAlgebra (s : Finset ι) :
    Algebra (MvPolynomial ι R) (coordinateLaurentAlgebra R s) :=
  (toCoordinateLaurent R s).toRingHom.toAlgebra

@[simp]
theorem algebraMap_coordinateLaurent (s : Finset ι) (p : MvPolynomial ι R) :
    algebraMap (MvPolynomial ι R) (coordinateLaurentAlgebra R s) p =
      toCoordinateLaurent R s p := rfl

instance coordinateLaurentScalarTower (s : Finset ι) :
    IsScalarTower R (MvPolynomial ι R) (coordinateLaurentAlgebra R s) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := MvPolynomial ι R)
    (A := coordinateLaurentAlgebra R s) (fun r => (toCoordinateLaurent R s).commutes r |>.symm)

/-- The native coordinate Laurent monoid algebra is a localization away from the coordinate
product, with its original polynomial map and coefficient action. -/
instance coordinateLaurent_isLocalization (s : Finset ι) :
    IsLocalization.Away (∏ i ∈ s, X i : MvPolynomial ι R) (coordinateLaurentAlgebra R s) where
  map_units := by
    rintro ⟨p, n, rfl⟩
    change IsUnit (toCoordinateLaurent R s ((∏ i ∈ s, X i) ^ n))
    rw [map_pow]
    exact (coordinateProductUnit R s).isUnit.pow n
  surj f := by
    obtain ⟨n, p, hp⟩ := coordinateLaurent_exists_denominator R s f
    refine ⟨(p, ⟨(∏ i ∈ s, X i) ^ n, n, rfl⟩), ?_⟩
    change f * toCoordinateLaurent R s ((∏ i ∈ s, X i) ^ n) = toCoordinateLaurent R s p
    rw [map_pow]
    exact hp.symm
  exists_of_eq := by
    intro p q h
    have h' : p = q := toCoordinateLaurent_injective R s h
    subst q
    exact ⟨1, rfl⟩

/-- The actual localization is canonically the Laurent monomial algebra, linearly over the
original coefficient ring. -/
def coordinateLocalizationEquiv (s : Finset ι) :
    Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R) ≃ₐ[R] coordinateLaurentAlgebra R s :=
  (IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
    (Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R))
    (coordinateLaurentAlgebra R s)).restrictScalars R

@[simp]
theorem coordinateLocalizationEquiv_algebraMap (s : Finset ι) (p : MvPolynomial ι R) :
    coordinateLocalizationEquiv R s
      (algebraMap (MvPolynomial ι R) (Localization.Away (∏ i ∈ s, X i)) p) =
        toCoordinateLaurent R s p :=
  (IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
    (Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R))
    (coordinateLaurentAlgebra R s)).commutes p

/-- The canonical localization equivalence sends a displayed fraction to its Laurent monomial
denominator formula. -/
theorem coordinateLocalizationEquiv_mk (s : Finset ι) (n : ℕ) (p : MvPolynomial ι R) :
    coordinateLocalizationEquiv R s
        (Localization.mk p ⟨(∏ i ∈ s, X i) ^ n, n, rfl⟩) =
      toCoordinateLaurent R s p *
        ((coordinateProductUnit R s ^ (-(n : ℤ)) : (coordinateLaurentAlgebra R s)ˣ) :
          coordinateLaurentAlgebra R s) := by
  change IsLocalization.algEquiv (Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
    (Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R)) (coordinateLaurentAlgebra R s)
      (Localization.mk p ⟨(∏ i ∈ s, X i) ^ n, n, rfl⟩) = _
  rw [Localization.mk_eq_mk', IsLocalization.algEquiv_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change toCoordinateLaurent R s p =
    (toCoordinateLaurent R s p * (coordinateProductUnit R s ^ (-(n : ℤ))).val) *
      toCoordinateLaurent R s ((∏ i ∈ s, X i) ^ n)
  rw [map_pow, mul_assoc]
  have hu : (coordinateProductUnit R s ^ (-(n : ℤ)) : (coordinateLaurentAlgebra R s)ˣ) *
      coordinateProductUnit R s ^ n = 1 := by simp
  have hv : (coordinateProductUnit R s ^ (-(n : ℤ))).val *
      toCoordinateLaurent R s (∏ i ∈ s, X i) ^ n = 1 := congrArg Units.val hu
  rw [hv, mul_one]

variable {R}

/-- Enlarging the inverted coordinate set includes the exponent monoids by the identity
on their actual integer exponent vectors. -/
def coordinateExponentInclusion {s t : Finset ι} (h : s ⊆ t) :
    coordinateExponentMonoid s →+ coordinateExponentMonoid t where
  toFun e := ⟨e.val, fun i hi => e.property i (fun his => hi (h his))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinateExponentInclusion_injective {s t : Finset ι} (h : s ⊆ t) :
    Function.Injective (coordinateExponentInclusion h) :=
  fun _ _ he => Subtype.ext (congrArg (fun z : coordinateExponentMonoid t => z.val) he)

variable (R)

/-- The canonical map between coordinate Laurent algebras fixes every coefficient and exponent. -/
def coordinateLaurentMap {s t : Finset ι} (h : s ⊆ t) :
    coordinateLaurentAlgebra R s →ₐ[R] coordinateLaurentAlgebra R t :=
  AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentInclusion h)

@[simp]
theorem coordinateLaurentMap_single {s t : Finset ι} (h : s ⊆ t)
    (e : coordinateExponentMonoid s) (r : R) :
    coordinateLaurentMap R h (AddMonoidAlgebra.single e r) =
      AddMonoidAlgebra.single (coordinateExponentInclusion h e) r :=
  AddMonoidAlgebra.mapDomain_single

theorem coordinateLaurentMap_injective {s t : Finset ι} (h : s ⊆ t) :
    Function.Injective (coordinateLaurentMap R h) :=
  AddMonoidAlgebra.mapDomain_injective (coordinateExponentInclusion_injective h)

/-- The Laurent restriction maps preserve the original polynomial map. -/
@[simp]
theorem coordinateLaurentMap_toCoordinateLaurent {s t : Finset ι} (h : s ⊆ t)
    (p : MvPolynomial ι R) :
    coordinateLaurentMap R h (toCoordinateLaurent R s p) = toCoordinateLaurent R t p := by
  change ((AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentInclusion h)).comp
    (AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentOfNat s))) p = _
  rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

@[simp]
theorem coordinateLaurentMap_refl (s : Finset ι) :
    coordinateLaurentMap R (Finset.Subset.refl s) = AlgHom.id R (coordinateLaurentAlgebra R s) := by
  change AddMonoidAlgebra.mapDomainAlgHom R R (AddMonoidHom.id _) = _
  exact AddMonoidAlgebra.mapDomainAlgHom_id

@[simp]
theorem coordinateLaurentMap_comp {s t v : Finset ι} (h : s ⊆ t) (k : t ⊆ v) :
    (coordinateLaurentMap R k).comp (coordinateLaurentMap R h) =
      coordinateLaurentMap R (h.trans k) := by
  change (AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentInclusion k)).comp
    (AddMonoidAlgebra.mapDomainAlgHom R R (coordinateExponentInclusion h)) = _
  rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- The original localization map obtained by inverting more coordinates. -/
def coordinateLocalizationMap {s t : Finset ι} (h : s ⊆ t) :
    Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R) →+*
      Localization.Away (∏ i ∈ t, X i : MvPolynomial ι R) :=
  Localization.awayLift
    (algebraMap (MvPolynomial ι R) (Localization.Away (∏ i ∈ t, X i))) (∏ i ∈ s, X i)
    (isUnit_of_dvd_unit (map_dvd _ (Finset.prod_dvd_prod_of_subset s t X h))
      (IsLocalization.Away.algebraMap_isUnit (∏ i ∈ t, X i)))

@[simp]
theorem coordinateLocalizationMap_algebraMap {s t : Finset ι} (h : s ⊆ t)
    (p : MvPolynomial ι R) :
    coordinateLocalizationMap R h
        (algebraMap (MvPolynomial ι R) (Localization.Away (∏ i ∈ s, X i)) p) =
      algebraMap (MvPolynomial ι R) (Localization.Away (∏ i ∈ t, X i)) p := by
  simp [coordinateLocalizationMap]

/-- The Laurent coefficient comparison identifies the actual localization map with the
coefficient/exponent-preserving inclusion. -/
theorem coordinateLocalizationEquiv_map {s t : Finset ι} (h : s ⊆ t)
    (x : Localization.Away (∏ i ∈ s, X i : MvPolynomial ι R)) :
    coordinateLocalizationEquiv R t (coordinateLocalizationMap R h x) =
      coordinateLaurentMap R h (coordinateLocalizationEquiv R s x) := by
  have H : (coordinateLocalizationEquiv R t).toRingHom.comp (coordinateLocalizationMap R h) =
      (coordinateLaurentMap R h).toRingHom.comp (coordinateLocalizationEquiv R s).toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
    apply RingHom.ext
    intro p
    simp
  exact RingHom.congr_fun H x

@[simp]
theorem coordinateLocalizationMap_refl (s : Finset ι) :
    coordinateLocalizationMap R (Finset.Subset.refl s) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
  apply RingHom.ext
  intro p
  simp

@[simp]
theorem coordinateLocalizationMap_comp {s t v : Finset ι} (h : s ⊆ t) (k : t ⊆ v) :
    (coordinateLocalizationMap R k).comp (coordinateLocalizationMap R h) =
      coordinateLocalizationMap R (h.trans k) := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (∏ i ∈ s, X i : MvPolynomial ι R))
  apply RingHom.ext
  intro p
  simp

end MvPolynomial
