/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinateLocalization
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The native grading of coordinate Laurent localizations

The integer total degree is the native `Finsupp.degree` of an exponent vector. Mathlib's
`AddMonoidAlgebra.gradeBy` supplies the graded algebra and its monomial degree pieces.
The canonical polynomial inclusion preserves and reflects the original homogeneous degrees.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace MvPolynomial

variable {ι : Type*}

/-- Total degree on the actual coordinate exponent monoid. -/
def coordinateDegree (s : Finset ι) : coordinateExponentMonoid s →+ ℤ :=
  Finsupp.degree.comp (coordinateExponentMonoid s).subtype

@[simp]
theorem coordinateDegree_ofNat (s : Finset ι) (e : ι →₀ ℕ) :
    coordinateDegree s (coordinateExponentOfNat s e) = (e.degree : ℤ) := by
  induction e using Finsupp.induction with
  | zero => simp [coordinateDegree]
  | @single_add i n e hi hn ih =>
    simp only [map_add, ih, Finsupp.degree_single, Nat.cast_add]
    congr 1
    simp [coordinateDegree, coordinateExponentOfNat]

@[simp]
theorem coordinateProductExponent_degree (s : Finset ι) :
    (coordinateProductExponent s).degree = s.card := by
  classical
  simp [coordinateProductExponent]

theorem coordinateDegree_product (s : Finset ι) :
    coordinateDegree s (coordinateExponentOfNat s (coordinateProductExponent s)) =
      (s.card : ℤ) := by
  rw [coordinateDegree_ofNat, coordinateProductExponent_degree]

@[simp]
theorem coordinateDegree_negativeProduct (s : Finset ι) :
    coordinateDegree s (coordinateNegativeProductExponent s) = -(s.card : ℤ) := by
  change Finsupp.degree (-(coordinateExponentOfNat s (coordinateProductExponent s)).val) = _
  rw [map_neg]
  exact congrArg Neg.neg (coordinateDegree_product s)

variable (R : Type*) [CommRing R]

/-- The native integer grading of the coordinate Laurent algebra. -/
abbrev coordinateGrading (s : Finset ι) : ℤ → Submodule R (coordinateLaurentAlgebra R s) :=
  AddMonoidAlgebra.gradeBy R (coordinateDegree s)

/-- The degree pieces are precisely the native submodules supported on exponents of that degree. -/
theorem coordinateGrading_eq_supported (s : Finset ι) (d : ℤ) :
    coordinateGrading R s d =
      AddMonoidAlgebra.supported R R
        {e : coordinateExponentMonoid s | coordinateDegree s e = d} := by
  ext f
  rfl

/-- The actual degree-`d` piece is free on the allowed degree-`d` Laurent exponents. -/
def coordinateGradeEquivFinsupp (s : Finset ι) (d : ℤ) :
    coordinateGrading R s d ≃ₗ[R]
      ({e : coordinateExponentMonoid s // coordinateDegree s e = d} →₀ R) :=
  (LinearEquiv.ofEq _ _ (coordinateGrading_eq_supported R s d)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R)
      {e : coordinateExponentMonoid s | coordinateDegree s e = d})

/-- The polynomial inclusion preserves each original coefficient at its cast exponent. -/
@[simp]
theorem toCoordinateLaurent_coeff (s : Finset ι) (p : MvPolynomial ι R) (e : ι →₀ ℕ) :
    (toCoordinateLaurent R s p).coeff (coordinateExponentOfNat s e) = p.coeff e := by
  change (Finsupp.mapDomain (coordinateExponentOfNat s) p.coeff)
    (coordinateExponentOfNat s e) = _
  exact Finsupp.mapDomain_apply_of_injective (coordinateExponentOfNat_injective s) _ _

/-- Membership of a polynomial image in an integer grade is measured by its original monomials. -/
theorem toCoordinateLaurent_mem_coordinateGrading_iff (s : Finset ι)
    (p : MvPolynomial ι R) (d : ℤ) :
    toCoordinateLaurent R s p ∈ coordinateGrading R s d ↔
      ∀ e ∈ p.support, (e.degree : ℤ) = d := by
  classical
  change (∀ e ∈ (Finsupp.mapDomain (coordinateExponentOfNat s) p.coeff).support,
    coordinateDegree s e = d) ↔ _
  rw [Finsupp.mapDomain_support_of_injective (coordinateExponentOfNat_injective s)]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    coordinateDegree_ofNat]
  rfl

/-- The canonical polynomial inclusion preserves and reflects its original homogeneous degrees. -/
theorem toCoordinateLaurent_homogeneous_iff (s : Finset ι) (p : MvPolynomial ι R) (n : ℕ) :
    toCoordinateLaurent R s p ∈ coordinateGrading R s (n : ℤ) ↔ p.IsHomogeneous n := by
  rw [toCoordinateLaurent_mem_coordinateGrading_iff]
  constructor
  · intro hp e he
    have hd : e.degree = n := by exact_mod_cast hp e (mem_support_iff.mpr he)
    simpa only [Finsupp.degree_eq_weight_one, ← Pi.one_def] using hd
  · intro hp e he
    have hd : e.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one, ← Pi.one_def] using hp (mem_support_iff.mp he)
    exact congrArg (fun k : ℕ => (k : ℤ)) hd

/-- The coordinate-product unit has its original total degree. -/
theorem coordinateProductUnit_mem_grade (s : Finset ι) :
    (coordinateProductUnit R s : coordinateLaurentAlgebra R s) ∈
      coordinateGrading R s (s.card : ℤ) := by
  change toCoordinateLaurent R s (∏ i ∈ s, X i) ∈ _
  rw [toCoordinateLaurent_coordinateProduct]
  simpa only [coordinateDegree_product] using
    (AddMonoidAlgebra.single_mem_gradeBy (coordinateDegree s)
      (coordinateExponentOfNat s (coordinateProductExponent s)) (1 : R))

/-- The inverse coordinate-product unit has the negative total degree. -/
theorem coordinateProductUnit_inv_mem_grade (s : Finset ι) :
    ((coordinateProductUnit R s)⁻¹ : (coordinateLaurentAlgebra R s)ˣ).val ∈
      coordinateGrading R s (-(s.card : ℤ)) := by
  change AddMonoidAlgebra.single (coordinateNegativeProductExponent s) (1 : R) ∈ _
  simpa only [coordinateDegree_negativeProduct] using
    (AddMonoidAlgebra.single_mem_gradeBy (coordinateDegree s)
      (coordinateNegativeProductExponent s) (1 : R))

/-- A negative natural power of the coordinate-product unit has the expected integer degree. -/
theorem coordinateProductUnit_neg_nat_mem_grade (s : Finset ι) (n : ℕ) :
    (coordinateProductUnit R s ^ (-(n : ℤ)) : (coordinateLaurentAlgebra R s)ˣ).val ∈
      coordinateGrading R s (-(n : ℤ) * (s.card : ℤ)) := by
  simpa only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val,
    nsmul_eq_mul, mul_neg, neg_mul] using
      SetLike.pow_mem_graded n (coordinateProductUnit_inv_mem_grade R s)

/-- The Laurent degree of an actual homogeneous fraction is numerator degree minus denominator
degree, through the canonical localization equivalence. -/
theorem coordinateLocalizationEquiv_mk_mem_grade (s : Finset ι) (n m : ℕ)
    (p : MvPolynomial ι R) (hp : p.IsHomogeneous m) :
    coordinateLocalizationEquiv R s
        (Localization.mk p ⟨(∏ i ∈ s, X i) ^ n, n, rfl⟩) ∈
      coordinateGrading R s ((m : ℤ) - (n : ℤ) * (s.card : ℤ)) := by
  rw [coordinateLocalizationEquiv_mk]
  simpa only [sub_eq_add_neg, neg_mul] using
    SetLike.mul_mem_graded ((toCoordinateLaurent_homogeneous_iff R s p m).mpr hp)
      (coordinateProductUnit_neg_nat_mem_grade R s n)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A product of distinct selected coordinates is homogeneous of the cardinality of the set. -/
theorem coordinateProduct_homogeneous (s : Finset ι) :
    (∏ i ∈ s, X i : MvPolynomial ι R) ∈ homogeneousSubmodule ι R s.card := by
  rw [mem_homogeneousSubmodule, coordinateProduct_eq_monomial]
  exact isHomogeneous_monomial 1 (coordinateProductExponent_degree s)

/-- The native homogeneous localization maps into the degree-zero Laurent piece. -/
theorem homogeneousLocalization_mem_coordinateZero (s : Finset ι)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i)) :
    coordinateLocalizationEquiv R s x.val ∈ coordinateGrading R s 0 := by
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousSubmodule ι R) (coordinateProduct_homogeneous R s) x
  have hp' : p.IsHomogeneous (n * s.card) := by
    simpa only [mem_homogeneousSubmodule, smul_eq_mul] using hp
  simpa only [HomogeneousLocalization.Away.val_mk, Nat.cast_mul, sub_self] using
    coordinateLocalizationEquiv_mk_mem_grade R s n (n * s.card) p hp'

/-- The canonical map from the native homogeneous localization to the actual Laurent
degree-zero ring. -/
def homogeneousLocalizationToCoordinateZero (s : Finset ι) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i) →+*
      coordinateGrading R s 0 where
  toFun x := ⟨coordinateLocalizationEquiv R s x.val,
    homogeneousLocalization_mem_coordinateZero R s x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem homogeneousLocalizationToCoordinateZero_injective (s : Finset ι) :
    Function.Injective (homogeneousLocalizationToCoordinateZero R s) := by
  intro x y h
  apply HomogeneousLocalization.val_injective
  apply (coordinateLocalizationEquiv R s).injective
  exact congrArg (fun z : coordinateGrading R s 0 => z.val) h

/-- Every degree-zero Laurent polynomial is represented by an actual homogeneous fraction. -/
theorem homogeneousLocalizationToCoordinateZero_surjective (s : Finset ι) :
    Function.Surjective (homogeneousLocalizationToCoordinateZero R s) := by
  intro f
  obtain ⟨n, p, hp⟩ := coordinateLaurent_exists_denominator R s f.val
  have hpgrade : toCoordinateLaurent R s p ∈ coordinateGrading R s ((n * s.card : ℕ) : ℤ) := by
    rw [hp]
    have h := SetLike.mul_mem_graded f.property
      (SetLike.pow_mem_graded n (coordinateProductUnit_mem_grade R s))
    simpa only [coordinateProductUnit, zero_add, nsmul_eq_mul, Nat.cast_mul] using h
  have hp' := (toCoordinateLaurent_homogeneous_iff R s p (n * s.card)).mp hpgrade
  let x := HomogeneousLocalization.Away.mk (homogeneousSubmodule ι R)
    (coordinateProduct_homogeneous R s) n p
      (by simpa only [mem_homogeneousSubmodule, smul_eq_mul] using hp')
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change coordinateLocalizationEquiv R s
    (Localization.mk p ⟨(∏ i ∈ s, X i) ^ n, n, rfl⟩) = f.val
  rw [coordinateLocalizationEquiv_mk, hp, mul_assoc]
  have hu : (coordinateProductUnit R s ^ n : (coordinateLaurentAlgebra R s)ˣ) *
      coordinateProductUnit R s ^ (-(n : ℤ)) = 1 := by simp
  have hv : toCoordinateLaurent R s (∏ i ∈ s, X i) ^ n *
      (coordinateProductUnit R s ^ (-(n : ℤ))).val = 1 := congrArg Units.val hu
  rw [hv, mul_one]

/-- The original degree-zero homogeneous localization is precisely the native degree-zero
Laurent ring, with the forward map induced by the actual localization equivalence. -/
def homogeneousLocalizationEquivCoordinateZero (s : Finset ι) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i) ≃+*
      coordinateGrading R s 0 :=
  RingEquiv.ofBijective (homogeneousLocalizationToCoordinateZero R s)
    ⟨homogeneousLocalizationToCoordinateZero_injective R s,
      homogeneousLocalizationToCoordinateZero_surjective R s⟩

/-- The degree-zero comparison retains the actual coefficient inclusion from
homogeneous constants. -/
theorem homogeneousLocalizationEquivCoordinateZero_fromZero (s : Finset ι) (r : R) :
    homogeneousLocalizationEquivCoordinateZero R s
        (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule ι R)
          (Submonoid.powers (∏ i ∈ s, X i)) ⟨C r, isHomogeneous_C ι r⟩) =
      algebraMap R (coordinateGrading R s 0) r := by
  apply Subtype.ext
  change coordinateLocalizationEquiv R s
      (algebraMap (MvPolynomial ι R) (Localization.Away (∏ i ∈ s, X i)) (C r)) =
    algebraMap R (coordinateLaurentAlgebra R s) r
  rw [coordinateLocalizationEquiv_algebraMap]
  exact (toCoordinateLaurent R s).commutes r

/-- Enlarging a coordinate intersection preserves each original Laurent degree. -/
theorem coordinateLaurentMap_mem_grade {s t : Finset ι} (h : s ⊆ t) {d : ℤ}
    {f : coordinateLaurentAlgebra R s} (hf : f ∈ coordinateGrading R s d) :
    coordinateLaurentMap R h f ∈ coordinateGrading R t d := by
  classical
  change ∀ e ∈ (Finsupp.mapDomain (coordinateExponentInclusion h) f.coeff).support,
    coordinateDegree t e = d
  rw [Finsupp.mapDomain_support_of_injective (coordinateExponentInclusion_injective h)]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact hf

/-- The original coordinate restriction map on each homogeneous Laurent module. -/
def coordinateLaurentDegreeMap {s t : Finset ι} (h : s ⊆ t) (d : ℤ) :
    coordinateGrading R s d →ₗ[R] coordinateGrading R t d where
  toFun f := ⟨coordinateLaurentMap R h f.val, coordinateLaurentMap_mem_grade R h f.property⟩
  map_add' f g := Subtype.ext (map_add (coordinateLaurentMap R h) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (coordinateLaurentMap R h) r f.val)

/-- The native Finsupp monomial coordinates are literally the original Laurent coefficients. -/
@[simp]
theorem coordinateGradeEquivFinsupp_apply (s : Finset ι) (d : ℤ)
    (f : coordinateGrading R s d)
    (e : {e : coordinateExponentMonoid s // coordinateDegree s e = d}) :
    coordinateGradeEquivFinsupp R s d f e = f.val.coeff e.val := rfl

variable {R}

/-- All integer powers of an inverted coordinate define allowed exponent vectors. -/
def coordinateSingleExponent (s : Finset ι) (i : ι) (hi : i ∈ s) :
    ℤ →+ coordinateExponentMonoid s where
  toFun d := ⟨Finsupp.single i d, by
    classical
    intro j hj
    have hji : i ≠ j := by intro h; subst j; exact hj hi
    simp [hji]⟩
  map_zero' := Subtype.ext (Finsupp.single_zero i)
  map_add' d e := Subtype.ext (Finsupp.single_add i d e)

@[simp]
theorem coordinateDegree_single (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    coordinateDegree s (coordinateSingleExponent s i hi d) = d :=
  Finsupp.degree_single i d

variable (R)

/-- The actual Laurent monomial `Xᵢ^d`, for an inverted coordinate and any integer exponent. -/
def coordinateVariableMonomial (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    coordinateLaurentAlgebra R s :=
  AddMonoidAlgebra.single (coordinateSingleExponent s i hi d) 1

@[simp]
theorem coordinateVariableMonomial_zero (s : Finset ι) (i : ι) (hi : i ∈ s) :
    coordinateVariableMonomial R s i hi 0 = 1 := by
  simp only [coordinateVariableMonomial, map_zero, AddMonoidAlgebra.one_def]

theorem coordinateVariableMonomial_mul (s : Finset ι) (i : ι) (hi : i ∈ s) (d e : ℤ) :
    coordinateVariableMonomial R s i hi d * coordinateVariableMonomial R s i hi e =
      coordinateVariableMonomial R s i hi (d + e) := by
  simp only [coordinateVariableMonomial, AddMonoidAlgebra.single_mul_single, ← map_add, one_mul]

/-- The integer powers of an inverted variable, as their original Laurent monomials. -/
def coordinateVariableMonomialHom (s : Finset ι) (i : ι) (hi : i ∈ s) :
    Multiplicative ℤ →* coordinateLaurentAlgebra R s where
  toFun d := coordinateVariableMonomial R s i hi d.toAdd
  map_one' := coordinateVariableMonomial_zero R s i hi
  map_mul' d e := (coordinateVariableMonomial_mul R s i hi d.toAdd e.toAdd).symm

/-- The actual unit given by an inverted coordinate, with inverse exponent `-1`. -/
def coordinateVariableUnit (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (coordinateLaurentAlgebra R s)ˣ :=
  (coordinateVariableMonomialHom R s i hi).toHomUnits (Multiplicative.ofAdd 1)

/-- Every integer power of the coordinate unit has its literal one-coordinate exponent. -/
@[simp]
theorem coordinateVariableUnit_zpow_val (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    (coordinateVariableUnit R s i hi ^ d).val = coordinateVariableMonomial R s i hi d := by
  change (((coordinateVariableMonomialHom R s i hi).toHomUnits
    (Multiplicative.ofAdd 1)) ^ d).val = _
  rw [← map_zpow (coordinateVariableMonomialHom R s i hi).toHomUnits]
  change coordinateVariableMonomial R s i hi (d • (1 : ℤ)) = _
  simp

/-- The original polynomial variable maps to the corresponding Laurent unit. -/
@[simp]
theorem toCoordinateLaurent_X (s : Finset ι) (i : ι) (hi : i ∈ s) :
    toCoordinateLaurent R s (X i) = (coordinateVariableUnit R s i hi).val := by
  classical
  change toCoordinateLaurent R s (monomial (Finsupp.single i 1) 1) =
    AddMonoidAlgebra.single (coordinateSingleExponent s i hi 1) 1
  rw [toCoordinateLaurent_monomial]
  congr 1
  apply Subtype.ext
  ext j
  simp [coordinateExponentOfNat, coordinateSingleExponent]

theorem coordinateVariableMonomial_mem_grade (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    coordinateVariableMonomial R s i hi d ∈ coordinateGrading R s d := by
  simpa only [coordinateVariableMonomial, coordinateDegree_single] using
    AddMonoidAlgebra.single_mem_gradeBy (coordinateDegree s)
      (coordinateSingleExponent s i hi d) (1 : R)

/-- Multiplication by the actual monomial `Xᵢ^d` identifies the degree-zero and degree-`d`
Laurent modules, with inverse multiplication by `Xᵢ^(-d)`. -/
def coordinateGradeShift (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    coordinateGrading R s 0 ≃ₗ[R] coordinateGrading R s d where
  toFun f := ⟨f.val * coordinateVariableMonomial R s i hi d, by
    simpa only [zero_add] using SetLike.mul_mem_graded f.property
      (coordinateVariableMonomial_mem_grade R s i hi d)⟩
  invFun f := ⟨f.val * coordinateVariableMonomial R s i hi (-d), by
    simpa only [add_neg_cancel] using SetLike.mul_mem_graded f.property
      (coordinateVariableMonomial_mem_grade R s i hi (-d))⟩
  left_inv f := by
    apply Subtype.ext
    change (f.val * coordinateVariableMonomial R s i hi d) *
      coordinateVariableMonomial R s i hi (-d) = f.val
    rw [mul_assoc, coordinateVariableMonomial_mul, add_neg_cancel,
      coordinateVariableMonomial_zero, mul_one]
  right_inv f := by
    apply Subtype.ext
    change (f.val * coordinateVariableMonomial R s i hi (-d)) *
      coordinateVariableMonomial R s i hi d = f.val
    rw [mul_assoc, coordinateVariableMonomial_mul, neg_add_cancel,
      coordinateVariableMonomial_zero, mul_one]
  map_add' f g := Subtype.ext (add_mul f.val g.val (coordinateVariableMonomial R s i hi d))
  map_smul' r f := Subtype.ext (smul_mul_assoc r f.val (coordinateVariableMonomial R s i hi d))

@[simp]
theorem coordinateGradeShift_apply (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : coordinateGrading R s 0) :
    (coordinateGradeShift R s i hi d f).val = f.val * coordinateVariableMonomial R s i hi d := rfl

/-- The original homogeneous-localization restriction obtained by inverting more coordinates. -/
def coordinateHomogeneousRestriction {s t : Finset ι} (h : s ⊆ t) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ t, X i) := by
  classical
  exact HomogeneousLocalization.awayMap (homogeneousSubmodule ι R)
    (coordinateProduct_homogeneous R (t \ s))
    ((Finset.prod_sdiff (f := fun i => (X i : MvPolynomial ι R)) h).symm.trans (mul_comm _ _))

/-- The homogeneous restriction has the original ordinary localization map as its underlying map. -/
theorem val_coordinateHomogeneousRestriction {s t : Finset ι} (h : s ⊆ t)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i)) :
    (coordinateHomogeneousRestriction R h x).val = coordinateLocalizationMap R h x.val := by
  classical
  rw [coordinateHomogeneousRestriction, HomogeneousLocalization.val_awayMap]
  rfl

/-- The degree-zero comparison identifies the actual homogeneous restriction map with the
original coefficient/exponent-preserving Laurent restriction. -/
theorem homogeneousLocalizationEquivCoordinateZero_restrict {s t : Finset ι} (h : s ⊆ t)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule ι R) (∏ i ∈ s, X i)) :
    homogeneousLocalizationEquivCoordinateZero R t (coordinateHomogeneousRestriction R h x) =
      coordinateLaurentDegreeMap R h 0 (homogeneousLocalizationEquivCoordinateZero R s x) := by
  apply Subtype.ext
  change coordinateLocalizationEquiv R t (coordinateHomogeneousRestriction R h x).val =
    coordinateLaurentMap R h (coordinateLocalizationEquiv R s x.val)
  rw [val_coordinateHomogeneousRestriction, coordinateLocalizationEquiv_map]

@[simp]
theorem coordinateHomogeneousRestriction_refl (s : Finset ι) :
    coordinateHomogeneousRestriction R (Finset.Subset.refl s) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply HomogeneousLocalization.val_injective
  simp [val_coordinateHomogeneousRestriction]

@[simp]
theorem coordinateHomogeneousRestriction_comp {s t v : Finset ι} (h : s ⊆ t) (k : t ⊆ v) :
    (coordinateHomogeneousRestriction R k).comp (coordinateHomogeneousRestriction R h) =
      coordinateHomogeneousRestriction R (h.trans k) := by
  apply RingHom.ext
  intro x
  apply HomogeneousLocalization.val_injective
  simp only [RingHom.comp_apply, val_coordinateHomogeneousRestriction]
  exact RingHom.congr_fun (coordinateLocalizationMap_comp R h k) x.val

/-- Laurent restriction preserves the actual selected-coordinate monomial. -/
@[simp]
theorem coordinateLaurentMap_variableMonomial {s t : Finset ι} (h : s ⊆ t)
    (i : ι) (hi : i ∈ s) (d : ℤ) :
    coordinateLaurentMap R h (coordinateVariableMonomial R s i hi d) =
      coordinateVariableMonomial R t i (h hi) d := by
  rw [coordinateVariableMonomial, coordinateLaurentMap_single]
  rfl

/-- Changing the inverted coordinate set commutes with the degree shift in the same
displayed coordinate frame. -/
theorem coordinateLaurentDegreeMap_gradeShift {s t : Finset ι} (h : s ⊆ t)
    (i : ι) (hi : i ∈ s) (d : ℤ) (f : coordinateGrading R s 0) :
    coordinateLaurentDegreeMap R h d (coordinateGradeShift R s i hi d f) =
      coordinateGradeShift R t i (h hi) d (coordinateLaurentDegreeMap R h 0 f) := by
  apply Subtype.ext
  change coordinateLaurentMap R h (f.val * coordinateVariableMonomial R s i hi d) = _
  rw [map_mul, coordinateLaurentMap_variableMonomial]
  rfl

end MvPolynomial
