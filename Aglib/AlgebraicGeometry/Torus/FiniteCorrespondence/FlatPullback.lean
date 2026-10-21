/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FibreLength
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModuleCycle

/-!
# FlatPullback for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FlatPullback.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d63b3f75dc365cd8f623ed21a658ca4d4fa0ff154f7be1cf72948e59d2f345ca`.

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
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [IsNoetherianRing S]

open Classical in
/-- Finite integer coefficients of the literal fibre over a source label. -/
def flatFibreCoefficients (p : FiniteDominantPrime R) : FiniteDominantPrime S →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun q => if q.val.under (Laurent R) = p.val then (residueFibreMultiplicity (R := R) q.val :
      ℤ) else 0)
    (by
      apply (finite_dominantFibre (S := S) p).subset
      intro q hq
      by_contra h
      change q.val.under (Laurent R) ≠ p.val at h
      exact hq (by simp [h]))

/-- The cycle of the flat scalar-extension fibre, with coefficients from the localized fibre
lengths. -/
def flatFibreCycle (p : FiniteDominantPrime R) : FreeAbelianGroup (FiniteDominantPrime S) :=
  Finsupp.toFreeAbelianGroup (flatFibreCoefficients (S := S) p)

open Classical in
theorem flatFibreCycle_coeff (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    FreeAbelianGroup.coeff q (flatFibreCycle (S := S) p) =
      if q.val.under (Laurent R) = p.val then (residueFibreMultiplicity (R := R) q.val : ℤ) else
        0 := by
  simp [FreeAbelianGroup.coeff, flatFibreCycle, flatFibreCoefficients]

/-- The finite-support pullback on the original ordinary prime-label group. -/
def flatPullback : FreeAbelianGroup (FiniteDominantPrime R) →+ FreeAbelianGroup
    (FiniteDominantPrime S) :=
  FreeAbelianGroup.lift (flatFibreCycle (S := S))

@[simp] theorem flatPullback_of (p : FiniteDominantPrime R) :
    flatPullback (S := S) (FreeAbelianGroup.of p) = flatFibreCycle (S := S) p :=
  FreeAbelianGroup.lift_apply_of _ _

open Classical in
theorem flatPullback_of_coeff (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    FreeAbelianGroup.coeff q (flatPullback (S := S) (FreeAbelianGroup.of p)) =
      if q.val.under (Laurent R) = p.val then (residueFibreMultiplicity (R := R) q.val : ℤ) else
        0 := by
  rw [flatPullback_of, flatFibreCycle_coeff]

theorem flatPullback_of_support (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    q ∈ (flatPullback (S := S) (FreeAbelianGroup.of p)).support ↔
      q.val.under (Laurent R) = p.val := by
  classical
  rw [FreeAbelianGroup.mem_support_iff, flatPullback_of_coeff]
  by_cases h : q.val.under (Laurent R) = p.val
  · simp [h, ne_of_gt (dominantFibreMultiplicity_pos p q h)]
  · simp [h]

/-- Every minimal component is represented in the constructed fibre cycle;
there is no discarded vertical or nonfinite component. -/
theorem flatPullback_contains_every_minimal [IsDomain R] [IsDomain S]
    (p : FiniteDominantPrime R) (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) :
    minimalFibrePoint p q hq ∈ (flatPullback (S := S) (FreeAbelianGroup.of p)).support :=
  (flatPullback_of_support p (minimalFibrePoint p q hq)).mpr (minimalFibre_under p q hq)

theorem flatPullback_support_minimal (p : FiniteDominantPrime R) (q : FiniteDominantPrime S)
    (hq : q ∈ (flatPullback (S := S) (FreeAbelianGroup.of p)).support) :
    q.val ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes :=
  (fibre_under_iff_minimal p q).mp ((flatPullback_of_support p q).mp hq)

theorem flatPullback_coeff_of_under (z : FreeAbelianGroup (FiniteDominantPrime R)) (p :
    FiniteDominantPrime R) (q : FiniteDominantPrime S)
    (h : q.val.under (Laurent R) = p.val) :
    FreeAbelianGroup.coeff q (flatPullback (S := S) z) =
      FreeAbelianGroup.coeff p z * (residueFibreMultiplicity (R := R) q.val : ℤ) := by
  classical
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of r =>
    rw [flatPullback_of_coeff, h]
    by_cases hr : r = p
    · subst r; simp [FreeAbelianGroup.coeff]
    · have hv : p.val ≠ r.val := fun he => hr (Subtype.ext he.symm)
      simp [hr, hv, FreeAbelianGroup.coeff]
  | neg r hr => simpa only [map_neg, neg_mul] using congrArg Neg.neg hr
  | add z w hz hw => simp only [map_add, hz, hw, add_mul]

theorem flatPullback_coeff_eq_zero_of_no_point (z : FreeAbelianGroup (FiniteDominantPrime R)) (q
    : FiniteDominantPrime S)
    (h : ∀ p : FiniteDominantPrime R, q.val.under (Laurent R) ≠ p.val) :
    FreeAbelianGroup.coeff q (flatPullback (S := S) z) = 0 := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => rw [flatPullback_of_coeff, ite_eq_right (h p)]
  | neg p hp => simpa only [map_neg, neg_zero] using congrArg Neg.neg hp
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]

omit [IsNoetherianRing S] in
/-- The matching-point coefficient formula, retaining its original target-Noetherian guard. -/
-- Retain the target-Noetherian guard of the original matching-point coefficient interface.
@[nolint unusedArguments]
theorem coefficient_flat_baseChange_of_matching_points [IsNoetherianRing S]
    (X : Object R) (p : FiniteDominantPrime R) (q : FiniteDominantPrime S)
    (h : q.val.under (Laurent R) = p.val) :
    coefficient (X.baseChange S) q =
      coefficient X p * residueFibreMultiplicity (R := R) q.val := by
  have hl : ambientLength (X.baseChange S) q.val =
      ambientLength X (q.val.under (Laurent R)) * residueFibreLength (R := R) q.val :=
    ambientLength_flat_baseChange X q.val
  simp only [h] at hl
  exact (congrArg ENat.toNat hl).trans (ENat.toNat_mul _ _)

/-- Full finite-cycle naturality for the original object over any flat map of
Noetherian domains, proved from its actual coefficients at every target label. -/
-- Retain the target-domain guard of the original flat object-cycle naturality interface.
@[nolint unusedArguments]
theorem objectCycle_flat_baseChange [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (X : Object R) :
    objectCycle (X.baseChange S) = flatPullback (S := S) (objectCycle X) := by
  classical
  apply (FreeAbelianGroup.equivFinsupp (FiniteDominantPrime S)).injective
  ext q
  change FreeAbelianGroup.coeff q (objectCycle (X.baseChange S)) =
    FreeAbelianGroup.coeff q (flatPullback (S := S) (objectCycle X))
  by_cases h : ∃ p : FiniteDominantPrime R, q.val.under (Laurent R) = p.val
  · obtain ⟨p, hp⟩ := h
    rw [flatPullback_coeff_of_under _ p q hp, objectCycle_coeff, objectCycle_coeff,
      coefficient_flat_baseChange_of_matching_points X p q hp, Nat.cast_mul]
  · have hn : ∀ p : FiniteDominantPrime R, q.val.under (Laurent R) ≠ p.val := by simpa using h
    rw [flatPullback_coeff_eq_zero_of_no_point _ q hn, objectCycle_coeff]
    have hc : coefficient (X.baseChange S) q = 0 := by
      by_contra hc
      have hq := (coefficient_ne_zero_iff (X.baseChange S) q).mp hc
      have hm := minimal_of_support_le (X.baseChange S) q.val q.under_eq_bot hq
      exact hn (contractedSupportPoint X q.val hm) rfl
    simp [hc]

end AlgebraicGeometry.Torus.FiniteCorrespondence
