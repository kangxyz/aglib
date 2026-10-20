/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PointModule

/-!
# FieldPullback for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FieldPullback.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9e4b842e33d347cf9cce8bec0d91266fe5b8e92d14ee88bef50c59e41bef038c`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A target label occurs in the scalar-extended point object precisely when
its literal contraction is the original label. No global point contraction. -/
theorem pointObject_baseChange_support_iff (p : FiniteDominantPrime K) (q : FiniteDominantPrime L) :
    supportIdeal ((pointObject p).baseChange L) ≤ q.val ↔
      q.val.under (Laurent K) = p.val := by
  constructor
  · intro hq
    have hm := minimal_of_support_le ((pointObject p).baseChange L) q.val q.under_eq_bot hq
    have hp := minimalSupport_baseChange_under (pointObject p) q.val hm
    rw [supportIdeal_pointObject, Ideal.minimalPrimes_eq_subsingleton_self] at hp
    exact Set.mem_singleton_iff.mp hp
  · intro hp
    rw [supportIdeal_baseChange, supportIdeal_pointObject]
    apply Ideal.map_le_iff_le_comap.mpr
    change p.val ≤ q.val.under (Laurent K)
    rw [hp]

/-- The fibre multiplicity is finite for every target label over a fixed
source label, independently of the Object whose cycle will be transported. -/
theorem fieldFibreLength_ne_top (p : FiniteDominantPrime K) (q : FiniteDominantPrime L)
    (h : q.val.under (Laurent K) = p.val) : residueFibreLength (R := K) q.val ≠ ⊤ :=
  residueFibreLength_ne_top (pointObject p) q.val
    (minimal_of_support_le ((pointObject p).baseChange L) q.val q.under_eq_bot
      ((pointObject_baseChange_support_iff p q).mpr h))

theorem fieldFibreMultiplicity_coe (p : FiniteDominantPrime K) (q : FiniteDominantPrime L)
    (h : q.val.under (Laurent K) = p.val) :
    (residueFibreMultiplicity (R := K) q.val : ℕ∞) = residueFibreLength (R := K) q.val :=
  ENat.natCast_toNat (fieldFibreLength_ne_top p q h)

theorem fieldFibreMultiplicity_pos (p : FiniteDominantPrime K) (q : FiniteDominantPrime L)
    (h : q.val.under (Laurent K) = p.val) : 0 < residueFibreMultiplicity (R := K) q.val := by
  have hn := residueFibreLength_ne_zero (R := K) q.val
  rw [← fieldFibreMultiplicity_coe p q h] at hn
  exact_mod_cast (pos_iff_ne_zero.mpr hn)

/-- The same literal local formula at any matching source and target labels,
including labels where an arbitrary object's coefficient vanishes. -/
theorem coefficient_field_baseChange_of_under (X : Object K) (p : FiniteDominantPrime K) (q :
    FiniteDominantPrime L)
    (h : q.val.under (Laurent K) = p.val) :
    coefficient (X.baseChange L) q =
      coefficient X p * residueFibreMultiplicity (R := K) q.val := by
  have hl : ambientLength (X.baseChange L) q.val =
      ambientLength X (q.val.under (Laurent K)) * residueFibreLength (R := K) q.val :=
    ambientLength_flat_baseChange X q.val
  simp only [h] at hl
  exact (congrArg ENat.toNat hl).trans (ENat.toNat_mul _ _)

open Classical in
/-- The actual scalar-extended point object carries precisely the fibre's
local length, with zero coefficient away from that fibre. -/
theorem coefficient_pointObject_baseChange (p : FiniteDominantPrime K) (q : FiniteDominantPrime L) :
    coefficient ((pointObject p).baseChange L) q =
      if q.val.under (Laurent K) = p.val then residueFibreMultiplicity (R := K) q.val else 0 := by
  by_cases h : q.val.under (Laurent K) = p.val
  · rw [ite_eq_left h, coefficient_field_baseChange_of_under (pointObject p) p q h,
      coefficient_pointObject_self, one_mul]
  · rw [ite_eq_right h]
    exact coefficient_baseChange_zero_off_support (pointObject p) q
      (fun hq => h ((pointObject_baseChange_support_iff p q).mp hq))

/-- Finite integral pullback on the actual free abelian group of prime labels.
The cycle of each scalar-extended original point object supplies finite support. -/
def fieldPullback : FreeAbelianGroup (FiniteDominantPrime K) →+ FreeAbelianGroup
    (FiniteDominantPrime L) :=
  FreeAbelianGroup.lift (fun p => objectCycle ((pointObject p).baseChange L))

@[simp] theorem fieldPullback_of (p : FiniteDominantPrime K) :
    fieldPullback (L := L) (FreeAbelianGroup.of p) = objectCycle ((pointObject p).baseChange L) :=
  FreeAbelianGroup.lift_apply_of _ _

open Classical in
/-- Exact generator coefficients; this identifies the constructed operator as
length-weighted fibre pullback, including inseparable nilpotent contributions. -/
theorem fieldPullback_of_coeff (p : FiniteDominantPrime K) (q : FiniteDominantPrime L) :
    FreeAbelianGroup.coeff q (fieldPullback (L := L) (FreeAbelianGroup.of p)) =
      if q.val.under (Laurent K) = p.val then (residueFibreMultiplicity (R := K) q.val : ℤ) else
        0 := by
  rw [fieldPullback_of, objectCycle_coeff, coefficient_pointObject_baseChange]
  split_ifs <;> rfl

/-- Each literal fibre over a finite source label is finite; its points are
exactly the finite support of the constructed generator pullback. -/
theorem fieldPullback_of_support (p : FiniteDominantPrime K) (q : FiniteDominantPrime L) :
    q ∈ (fieldPullback (L := L) (FreeAbelianGroup.of p)).support ↔
      q.val.under (Laurent K) = p.val := by
  classical
  rw [FreeAbelianGroup.mem_support_iff, fieldPullback_of_coeff]
  by_cases h : q.val.under (Laurent K) = p.val
  · simp [h, ne_of_gt (fieldFibreMultiplicity_pos p q h)]
  · simp [h]

theorem finite_fieldFibre (p : FiniteDominantPrime K) :
    {q : FiniteDominantPrime L | q.val.under (Laurent K) = p.val}.Finite := by
  have hs : {q : FiniteDominantPrime L | q.val.under (Laurent K) = p.val} =
      ↑(fieldPullback (L := L) (FreeAbelianGroup.of p)).support := by
    ext q
    exact (fieldPullback_of_support p q).symm
  rw [hs]
  exact Finset.finite_toSet _

/-- At a target with a given source label, coefficients are multiplied by the
literal fibre multiplicity. Linearity automatically handles coincident labels. -/
theorem fieldPullback_coeff_of_under (z : FreeAbelianGroup (FiniteDominantPrime K)) (p :
    FiniteDominantPrime K) (q : FiniteDominantPrime L)
    (h : q.val.under (Laurent K) = p.val) :
    FreeAbelianGroup.coeff q (fieldPullback (L := L) z) =
      FreeAbelianGroup.coeff p z * (residueFibreMultiplicity (R := K) q.val : ℤ) := by
  classical
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of r =>
    rw [fieldPullback_of_coeff, h]
    by_cases hr : r = p
    · subst r; simp [FreeAbelianGroup.coeff]
    · have hv : p.val ≠ r.val := fun he => hr (Subtype.ext he.symm)
      simp [hr, hv, FreeAbelianGroup.coeff]
  | neg r hr => simpa only [map_neg, neg_mul] using congrArg Neg.neg hr
  | add z w hz hw => simp only [map_add, hz, hw, add_mul]

/-- A target label with no finite source label has zero pullback coefficient.
No artificial source point is constructed for it. -/
theorem fieldPullback_coeff_eq_zero_of_no_point (z : FreeAbelianGroup (FiniteDominantPrime K)) (q
    : FiniteDominantPrime L)
    (h : ∀ p : FiniteDominantPrime K, q.val.under (Laurent K) ≠ p.val) :
    FreeAbelianGroup.coeff q (fieldPullback (L := L) z) = 0 := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => rw [fieldPullback_of_coeff, ite_eq_right (h p)]
  | neg p hp => simpa only [map_neg, neg_zero] using congrArg Neg.neg hp
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]

/-- Naturality for every actual original Module.CommutingAutomorphisms object and arbitrary field
extension. The module, support and all local fibre multiplicities are derived. -/
theorem objectCycle_field_baseChange (X : Object K) :
    objectCycle (X.baseChange L) = fieldPullback (L := L) (objectCycle X) := by
  classical
  apply cycle_eq_of_coeff_eq
  intro q
  by_cases h : ∃ p : FiniteDominantPrime K, q.val.under (Laurent K) = p.val
  · obtain ⟨p, hp⟩ := h
    rw [fieldPullback_coeff_of_under _ p q hp, objectCycle_coeff, objectCycle_coeff,
      coefficient_field_baseChange_of_under X p q hp, Nat.cast_mul]
  · have hn : ∀ p : FiniteDominantPrime K, q.val.under (Laurent K) ≠ p.val := by simpa using h
    rw [fieldPullback_coeff_eq_zero_of_no_point _ q hn, objectCycle_coeff]
    have hc : coefficient (X.baseChange L) q = 0 := by
      by_contra hc
      have hq := (coefficient_ne_zero_iff (X.baseChange L) q).mp hc
      have hm := minimal_of_support_le (X.baseChange L) q.val q.under_eq_bot hq
      exact hn (contractedSupportPoint X q.val hm) rfl
    simp [hc]

end AlgebraicGeometry.Torus.FiniteCorrespondence
