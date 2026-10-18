/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.RationalExactness
public import Aglib.KTheory.MilnorK.InfinityDegree
public import Aglib.KTheory.MilnorK.Residue.Product

/-!
# Polynomial-presentation norms in every Milnor degree

The negative actual infinity residue descends through the constant image.
The proved all-degree rational residue equivalence then defines a total norm
on the actual dependent finite sum, with polynomial-presentation components.
Every actual lift computes the same value, finite-rational reciprocity holds,
and restriction from the base field followed by the norm is multiplication
by the polynomial degree. Genuine maps into the polynomial valuation rings
give the left base-field projection formula on arbitrary quotient classes.
The empty tuple and arbitrary characteristic are included.

These are norms for a specified monic irreducible polynomial presentation.
No independence from a primitive element or polynomial presentation, arbitrary
extension tower law, or curve reciprocity is asserted.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue

variable {k : Type*} [Field k]

/-- The negative infinity residue kills the entire actual constant image. -/
theorem constant_range_le_ker_neg_infinity (n : ℕ) :
    LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) ≤
      LinearMap.ker (-InfinityResidue.residue k n) := by
  rintro _ ⟨x, rfl⟩
  change -InfinityResidue.residue k n (MilnorK.map (n + 1) RatFunc.C x) = 0
  rw [InfinityResidue.residue_constants, neg_zero]

/-- The negative actual infinity residue descended by its proved vanishing. -/
def quotientNorm (n : ℕ) :
    (K (RatFunc k) (n + 1) ⧸
      LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k))) →ₗ[ℤ] K k n :=
  (LinearMap.range (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k))).liftQ
    (-InfinityResidue.residue k n) (constant_range_le_ker_neg_infinity n)

@[simp] theorem quotientNorm_mk (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    quotientNorm n (Submodule.Quotient.mk x) = -InfinityResidue.residue k n x := rfl

/-- The actual total norm on the original dependent finite residue vector. -/
def totalNorm (n : ℕ) :
    (Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) →ₗ[ℤ] K k n :=
  (quotientNorm n).comp (quotientConstantEquivResidues n).symm.toLinearMap

/-- The constructed total norm computes minus the actual infinity residue. -/
@[simp] theorem totalNorm_totalResidue (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    totalNorm n (totalResidue n x) = -InfinityResidue.residue k n x := by
  rw [← quotientConstantEquivResidues_mk n x]
  simp only [totalNorm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, quotientNorm_mk]

/-- Any actual rational lift computes the same value. -/
theorem totalNorm_eq_neg_residue_of_lift (n : ℕ)
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n)
    (x : K (RatFunc k) (n + 1)) (hx : totalResidue n x = y) :
    totalNorm n y = -InfinityResidue.residue k n x := by
  rw [← hx, totalNorm_totalResidue]

/-- Equality of actual finite residue vectors forces equality at infinity. -/
theorem infinity_residue_eq_of_totalResidue_eq (n : ℕ)
    (x y : K (RatFunc k) (n + 1)) (h : totalResidue n x = totalResidue n y) :
    InfinityResidue.residue k n x = InfinityResidue.residue k n y := by
  have hnorm := congrArg (totalNorm n) h
  simpa only [totalNorm_totalResidue, neg_inj] using hnorm

/-- The actual rational-function identity as an equality of linear maps. -/
theorem totalNorm_comp_totalResidue (n : ℕ) :
    (totalNorm (k := k) n).comp (totalResidue n) = -InfinityResidue.residue k n := by
  apply LinearMap.ext
  intro x
  exact totalNorm_totalResidue n x

/-- Actual finite-residue surjectivity makes the total norm unique. -/
theorem totalNorm_unique (n : ℕ)
    (f : (Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) →ₗ[ℤ] K k n)
    (hf : ∀ x : K (RatFunc k) (n + 1),
      f (totalResidue n x) = -InfinityResidue.residue k n x) :
    f = totalNorm n := by
  ext y
  obtain ⟨x, rfl⟩ := totalResidue_surjective n y
  exact (hf x).trans (totalNorm_totalResidue n x).symm

/-- The norm for a specified monic irreducible polynomial presentation. -/
def polynomialNorm (n : ℕ) (p : MonicIrreducible k) :
    K (AdjoinRoot p.val) n →ₗ[ℤ] K k n := by
  classical
  exact (totalNorm n).comp (DFinsupp.lsingle (R := ℤ)
    (M := fun q : MonicIrreducible k => K (AdjoinRoot q.val) n) p)

@[simp] theorem totalNorm_single [DecidableEq (MonicIrreducible k)]
    (n : ℕ) (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) n) :
    totalNorm n (DFinsupp.single p x) = polynomialNorm n p x := by
  simp only [polynomialNorm, LinearMap.comp_apply, DFinsupp.lsingle_apply]
  congr 1
  apply DFinsupp.ext
  intro q
  by_cases h : q = p
  · subst q
    simp only [DFinsupp.single_eq_same]
  · simp only [DFinsupp.single_apply]

open scoped Classical in
/-- Any actual lift supported at one place computes its polynomial norm. -/
theorem polynomialNorm_eq_neg_residue_of_lift (n : ℕ) (p : MonicIrreducible k)
    (y : K (AdjoinRoot p.val) n) (x : K (RatFunc k) (n + 1))
    (hx : totalResidue n x = DFinsupp.single p y) :
    polynomialNorm n p y = -InfinityResidue.residue k n x := by
  rw [← totalNorm_single, ← hx, totalNorm_totalResidue]

/-- Summing the polynomial components recovers the total norm. -/
theorem lsum_polynomialNorm [DecidableEq (MonicIrreducible k)] (n : ℕ) :
    DFinsupp.lsum ℤ (polynomialNorm (k := k) n) = totalNorm n := by
  apply DFinsupp.lhom_ext
  intro p x
  rw [DFinsupp.lsum_single, totalNorm_single]

open scoped Classical in
/-- The total norm sums over the genuine finite support of its input. -/
theorem totalNorm_eq_sum (n : ℕ)
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) :
    totalNorm n y = ∑ p ∈ y.support, polynomialNorm n p (y p) := by
  rw [← lsum_polynomialNorm]
  simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, DFinsupp.sum]

open scoped Classical in
/-- Actual finite-rational reciprocity, in every original base-field Milnor group. -/
theorem finite_rational_reciprocity (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    (∑ p ∈ (totalResidue n x).support, polynomialNorm n p (residueAt p.val n x)) +
      InfinityResidue.residue k n x = 0 := by
  change (∑ p ∈ (totalResidue n x).support, polynomialNorm n p (totalResidue n x p)) + _ = 0
  rw [← totalNorm_eq_sum, totalNorm_totalResidue, neg_add_cancel]

/-- Distinct monic irreducible polynomials cannot divide one another. -/
theorem not_dvd_of_ne (p q : MonicIrreducible k) (hpq : p ≠ q) : ¬ q.val ∣ p.val := by
  intro h
  apply hpq
  apply Subtype.ext
  exact eq_of_monic_of_associated p.property.1 q.property.1
    (q.property.2.associated_of_dvd p.property.2 h).symm

/-- Every finite place is prime to every nonzero constant polynomial. -/
theorem not_dvd_constant (p : MonicIrreducible k) (a : kˣ) : ¬ p.val ∣ C (a : k) :=
  p.property.1.not_dvd_of_natDegree_lt (C_ne_zero.mpr a.ne_zero)
    (by simpa only [natDegree_C] using p.property.2.natDegree_pos)

/-- Reduction of a constant polynomial unit is the literal base-field unit map. -/
theorem quotientUnit_constant (p : MonicIrreducible k) (a : kˣ) :
    quotientUnit p.val (C (a : k)) (not_dvd_constant p a) =
      Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a := by
  apply Units.ext
  rfl

/-- Constants followed by a polynomial have exactly its single finite residue. -/
theorem totalResidue_polynomial_constants [DecidableEq (MonicIrreducible k)]
    (n : ℕ) (p : MonicIrreducible k) (a : SymbolTuple k n) :
    totalResidue n (symbol (Fin.snoc (InfinityResidue.constantUnit k ∘ a)
      (polynomialUnit p.val p.property.2.ne_zero))) =
      DFinsupp.single p (MilnorK.map n (algebraMap k (AdjoinRoot p.val)) (symbol a)) := by
  classical
  apply DFinsupp.ext
  intro q
  rw [totalResidue_apply, ← InfinityResidue.polynomialUnit_constant_tuple]
  by_cases hpq : p = q
  · subst q
    rw [DFinsupp.single_eq_same, residueAt_polynomial_units p.val n
      (fun i => C (a i : k)) (fun i => C_ne_zero.mpr (a i).ne_zero)
      (fun i => not_dvd_constant p (a i)), MilnorK.map_symbol]
    congr 1
    funext i
    exact quotientUnit_constant p (a i)
  · rw [DFinsupp.single_eq_of_ne (Ne.symm hpq)]
    let r : Fin (n + 1) → k[X] := Fin.snoc (fun i => C (a i : k)) p.val
    have hr : ∀ i, r i ≠ 0 := by
      intro i
      cases i using Fin.lastCases with
      | last => simpa only [r, Fin.snoc_last] using p.property.2.ne_zero
      | cast i => simpa only [r, Fin.snoc_castSucc] using C_ne_zero.mpr (a i).ne_zero
    have hqr : ∀ i, ¬ q.val ∣ r i := by
      intro i
      cases i using Fin.lastCases with
      | last => simpa only [r, Fin.snoc_last] using not_dvd_of_ne p q hpq
      | cast i => simpa only [r, Fin.snoc_castSucc] using not_dvd_constant q (a i)
    have ht : (fun i => polynomialUnit (r i) (hr i)) =
        Fin.snoc (fun i => polynomialUnit (C (a i : k)) (C_ne_zero.mpr (a i).ne_zero))
          (polynomialUnit p.val p.property.2.ne_zero) := by
      funext i
      cases i using Fin.lastCases with
      | last => simp only [r, Fin.snoc_last]
      | cast i => simp only [r, Fin.snoc_castSucc]
    rw [← ht]
    exact residueAt_polynomial_units_zero q.val n r hr hqr

/-- The polynomial norm has positive degree on base-field symbols, including the empty tuple. -/
theorem polynomialNorm_map_constant_symbol (n : ℕ) (p : MonicIrreducible k)
    (a : SymbolTuple k n) :
    polynomialNorm n p (MilnorK.map n (algebraMap k (AdjoinRoot p.val)) (symbol a)) =
      (p.val.natDegree : ℤ) • symbol a := by
  classical
  rw [← totalNorm_single, ← totalResidue_polynomial_constants,
    totalNorm_totalResidue, InfinityResidue.residue_polynomial_constants]
  simp only [neg_smul, neg_neg]

/-- Restriction followed by the polynomial norm is multiplication by its degree. -/
theorem polynomialNorm_comp_constants (n : ℕ) (p : MonicIrreducible k) :
    (polynomialNorm n p).comp (MilnorK.map n (algebraMap k (AdjoinRoot p.val))) =
      (p.val.natDegree : ℤ) • LinearMap.id := by
  apply MilnorK.linearMap_ext
  intro a
  exact polynomialNorm_map_constant_symbol n p a

/-- The degree law applies to every base-field Milnor class in every nonnegative degree. -/
theorem polynomialNorm_map_constants (n : ℕ) (p : MonicIrreducible k) (x : K k n) :
    polynomialNorm n p (MilnorK.map n (algebraMap k (AdjoinRoot p.val)) x) =
      (p.val.natDegree : ℤ) • x :=
  LinearMap.congr_fun (polynomialNorm_comp_constants n p) x

/-- At each actual polynomial DVR, restriction from the base field acts on
residues by left multiplication. The field maps into the valuation ring first. -/
theorem residueAt_product_constants_left (p : k[X]) [Fact (Irreducible p)]
    (m n : ℕ) (x : K k m) (z : K (RatFunc k) (n + 1)) :
    residueAt p (m + n)
      (product m (n + 1) (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x) z) =
      product m n (MilnorK.map m (algebraMap k (AdjoinRoot p)) x) (residueAt p n z) := by
  let f : k →+* Polynomial.LocalResidue.Ring p :=
    (algebraMap k[X] (Polynomial.LocalResidue.Ring p)).comp C
  have hfield : (algebraMap (Polynomial.LocalResidue.Ring p) (RatFunc k)).comp f =
      (RatFunc.C : k →+* RatFunc k) := by
    ext a
    exact (IsScalarTower.algebraMap_apply k[X]
      (Polynomial.LocalResidue.Ring p) (RatFunc k) (C a)).symm
  have hred : (Polynomial.LocalResidue.residueEquiv p).toRingHom.comp
      ((IsLocalRing.residue (Polynomial.LocalResidue.Ring p)).comp f) =
      algebraMap k (AdjoinRoot p) := by
    ext a
    change Polynomial.LocalResidue.residueEquiv p
      (IsLocalRing.residue (Polynomial.LocalResidue.Ring p)
        (algebraMap k[X] (Polynomial.LocalResidue.Ring p) (C a))) = _
    rw [Polynomial.LocalResidue.residueEquiv_residue_polynomial]
    rfl
  have h := DVR.residue_product_base_field_left
    (Polynomial.LocalResidue.Ring p) (RatFunc k) f m n x z
  rw [hfield] at h
  have hm : MilnorK.map m (Polynomial.LocalResidue.residueEquiv p).toRingHom
      (MilnorK.map m ((IsLocalRing.residue (Polynomial.LocalResidue.Ring p)).comp f) x) =
      MilnorK.map m (algebraMap k (AdjoinRoot p)) x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hred]
  simpa only [degreeCongr_refl, residueAt_eq_dvr, LinearMap.comp_apply, map_product, hm] using
    congrArg (MilnorK.map (m + n) (Polynomial.LocalResidue.residueEquiv p).toRingHom) h

/-- Infinity has the same left base-field product formula, with actual inversion
and evaluation maps. There is no sign from moving a factor across the residue. -/
theorem infinity_product_constants_left (m n : ℕ) (x : K k m)
    (z : K (RatFunc k) (n + 1)) :
    InfinityResidue.residue k (m + n)
      (product m (n + 1) (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x) z) =
      product m n x (InfinityResidue.residue k n z) := by
  let : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
  have hfix : (RatFunc.inversion k).toRingHom.comp (RatFunc.C : k →+* RatFunc k) =
      (RatFunc.C : k →+* RatFunc k) := by
    ext a
    exact RatFunc.inversion_C k a
  have hinv : MilnorK.map m (RatFunc.inversion k).toRingHom
      (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x) =
      MilnorK.map m (RatFunc.C : k →+* RatFunc k) x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hfix]
  have hroot : (InfinityResidue.rootXEquiv k).toRingHom.comp
      (algebraMap k (AdjoinRoot (X : k[X]))) = RingHom.id k := by
    ext a
    exact (InfinityResidue.rootXEquiv k).commutes a
  have hbase : MilnorK.map m (InfinityResidue.rootXEquiv k).toRingHom
      (MilnorK.map m (algebraMap k (AdjoinRoot (X : k[X]))) x) = x := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hroot, MilnorK.map_id,
      LinearMap.id_apply]
  have hprod : MilnorK.map (m + n + 1) (RatFunc.inversion k).toRingHom
      (product m (n + 1) (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x) z) =
      product m (n + 1)
        (MilnorK.map m (RatFunc.inversion k).toRingHom
          (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x))
        (MilnorK.map (n + 1) (RatFunc.inversion k).toRingHom z) :=
    map_product (RatFunc.inversion k).toRingHom _ _
  simp only [InfinityResidue.residue, LinearMap.comp_apply]
  rw [hprod, hinv, residueAt_product_constants_left, map_product, hbase]

/-- Left multiplication by a base-field class, separately on each original
finite residue-field group. Its support is finite by zero preservation. -/
def residueProductLeft (m n : ℕ) (x : K k m) :
    (Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) →ₗ[ℤ]
      Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) (m + n) :=
  DFinsupp.mapRange.linearMap fun p =>
    product m n (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x)

@[simp] theorem residueProductLeft_apply (m n : ℕ) (x : K k m)
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) (p : MonicIrreducible k) :
    residueProductLeft m n x y p =
      product m n (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x) (y p) := rfl

@[simp] theorem residueProductLeft_single [DecidableEq (MonicIrreducible k)]
    (m n : ℕ) (x : K k m) (p : MonicIrreducible k) (y : K (AdjoinRoot p.val) n) :
    residueProductLeft m n x (DFinsupp.single p y) =
      DFinsupp.single p (product m n (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x) y) := by
  simp only [residueProductLeft, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]

/-- The actual finite residue vector commutes with left base-field multiplication. -/
theorem totalResidue_product_constants_left (m n : ℕ) (x : K k m)
    (z : K (RatFunc k) (n + 1)) :
    totalResidue (m + n)
      (product m (n + 1) (MilnorK.map m (RatFunc.C : k →+* RatFunc k) x) z) =
      residueProductLeft m n x (totalResidue n z) := by
  apply DFinsupp.ext
  intro p
  exact residueAt_product_constants_left p.val m n x z

/-- The total norm satisfies the left projection formula for arbitrary
base-field classes and arbitrary actual finite residue vectors. -/
theorem totalNorm_product_constants_left (m n : ℕ) (x : K k m)
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n) :
    totalNorm (m + n) (residueProductLeft m n x y) = product m n x (totalNorm n y) := by
  obtain ⟨z, rfl⟩ := totalResidue_surjective n y
  rw [← totalResidue_product_constants_left, totalNorm_totalResidue,
    infinity_product_constants_left, totalNorm_totalResidue, map_neg]

/-- A chosen polynomial-presentation norm satisfies the left base-field
projection formula on arbitrary quotient classes in both factors. -/
theorem polynomialNorm_product_constants_left (m n : ℕ) (p : MonicIrreducible k)
    (x : K k m) (y : K (AdjoinRoot p.val) n) :
    polynomialNorm (m + n) p
      (product m n (MilnorK.map m (algebraMap k (AdjoinRoot p.val)) x) y) =
      product m n x (polynomialNorm n p y) := by
  classical
  simpa only [residueProductLeft_single, totalNorm_single] using
    totalNorm_product_constants_left m n x (DFinsupp.single p y)

end MilnorK.PolynomialNorm
