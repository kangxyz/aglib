/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.Tactic.LinearCombination

/-!
# A monic quadratic on its discriminant localization

General declarations extracted from R5 baseline
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; names, chosen maps and hypotheses retained.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/QuadraticDiscriminant.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5d69774d84467db5f4abb4aba1486f10286c2effe982a2e31e3c6966edcd5d16`.
-/

@[expose] public section

noncomputable section
open Polynomial
open scoped Polynomial

namespace Algebra.QuadraticDiscriminant
variable {R : Type*} [CommRing R]

def poly (q : R) : R[X] := X ^ 2 - X - C q

lemma poly_monic (q : R) : (poly q).Monic := by
  rw [poly, sub_sub]
  exact monic_X_pow_sub (by
    apply lt_of_le_of_lt (degree_add_le _ _)
    exact max_lt (lt_of_le_of_lt degree_X_le (by norm_num))
      (lt_of_le_of_lt degree_C_le (by norm_num)))

lemma root_relation (q : R) :
    AdjoinRoot.root (poly q) ^ 2 - AdjoinRoot.root (poly q) =
      algebraMap R (AdjoinRoot (poly q)) q := by
  have h := AdjoinRoot.mk_self (f := poly q)
  change AdjoinRoot.mk (poly q) (X ^ 2 - X - C q) = 0 at h
  rw [map_sub, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

lemma exists_normalForm (q : R) (x : AdjoinRoot (poly q)) :
    ∃ a b : R, x = algebraMap R _ a + algebraMap R _ b * AdjoinRoot.root (poly q) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  induction p using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by simp [AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]⟩
  | add p r hp hr =>
    obtain ⟨a, b, ha⟩ := hp
    obtain ⟨c, d, hc⟩ := hr
    refine ⟨a + c, b + d, ?_⟩
    rw [map_add, ha, hc, map_add, map_add]
    ring
  | monomial n c h =>
    obtain ⟨a, b, ha⟩ := h
    refine ⟨b * q, a + b, ?_⟩
    have hx := root_relation q
    rw [pow_succ, ← mul_assoc, map_mul, ha, AdjoinRoot.mk_X, map_mul, map_add]
    linear_combination algebraMap R (AdjoinRoot (poly q)) b * hx

/-- The discriminant localization of a monic quadratic is standard étale,
including in characteristic two. -/
def standardPair (q : R) : StandardEtalePair R where
  f := poly q
  monic_f := poly_monic q
  g := C (1 + 4 * q)
  cond := by
    refine ⟨2 * X - 1, -4, 1, ?_⟩
    simp only [poly, derivative_sub, derivative_pow, derivative_X, derivative_C,
      pow_one, Nat.cast_ofNat, mul_one, sub_zero, map_add, map_one, map_mul, map_ofNat]
    ring

abbrev Away (q : R) :=
  Localization.Away (algebraMap R (AdjoinRoot (poly q)) (1 + 4 * q))

instance away_etale (q : R) : Algebra.Etale R (Away q) := by
  exact Algebra.Etale.of_equiv (standardPair q).equivAwayAdjoinRoot

end Algebra.QuadraticDiscriminant
