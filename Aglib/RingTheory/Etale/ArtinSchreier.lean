/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The finite etale Artin--Schreier root algebra

The actual quotient by `X^p - X - a` is finite free and etale over every
commutative ring in which `p = 0`, including the zero ring. Its distinguished root solves the
original equation. This supplies the algebraic cover for etale-local
surjectivity in the Artin--Schreier sequence.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.ArtinSchreier

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]

/-- The polynomial defining an Artin--Schreier root. -/
def poly (a : R) : R[X] := X ^ p - X - C a

private lemma degree_remainder_lt (a : R) : degree (X + C a : R[X]) < p := by
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt degree_X_le (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (Fact.out : p.Prime).pos)

lemma poly_monic (a : R) : (poly p a).Monic := by
  rw [poly, sub_sub]
  exact monic_X_pow_sub (degree_remainder_lt p a)

lemma degree_poly [Nontrivial R] (a : R) : (poly p a).degree = p := by
  have hlt : degree (X + C a : R[X]) < degree ((X : R[X]) ^ p) := by
    simpa only [degree_X_pow] using degree_remainder_lt p a
  rw [poly, sub_sub, degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]

omit [Fact p.Prime] in
lemma derivative_poly_of_cast_eq_zero (a : R) (hp : (p : R) = 0) :
    (poly p a).derivative = -1 := by
  simp [poly, derivative_pow, hp]

omit [Fact p.Prime] in
lemma derivative_poly [CharP R p] (a : R) : (poly p a).derivative = -1 :=
  derivative_poly_of_cast_eq_zero p a (CharP.cast_eq_zero R p)

/-- The original quotient algebra adjoining an Artin--Schreier root. -/
abbrev RootAlgebra (a : R) := AdjoinRoot (poly p a)

instance rootAlgebra_free (a : R) : Module.Free R (RootAlgebra p a) :=
  (poly_monic p a).free_adjoinRoot

instance rootAlgebra_finite (a : R) : Module.Finite R (RootAlgebra p a) :=
  (poly_monic p a).finite_adjoinRoot

omit [Fact p.Prime] in
/-- The distinguished quotient root satisfies the original Artin--Schreier equation. -/
lemma root_relation (a : R) :
    AdjoinRoot.root (poly p a) ^ p - AdjoinRoot.root (poly p a) =
      algebraMap R (RootAlgebra p a) a := by
  have h := AdjoinRoot.mk_self (f := poly p a)
  change AdjoinRoot.mk (poly p a) (X ^ p - X - C a) = 0 at h
  rw [map_sub, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

/-- A standard-etale presentation using only the equation `p = 0` in the base. -/
def standardPairOfCastEqZero (a : R) (hp : (p : R) = 0) : StandardEtalePair R where
  f := poly p a
  monic_f := poly_monic p a
  g := 1
  cond := ⟨-1, 0, 0, by simp [derivative_poly_of_cast_eq_zero p a hp]⟩

/-- The derivative is a unit, so no additional localization is needed. -/
def standardPair [CharP R p] (a : R) : StandardEtalePair R :=
  standardPairOfCastEqZero p a (CharP.cast_eq_zero R p)

/-- The root algebra is etale whenever `p = 0` in the base, including the zero ring. -/
lemma rootAlgebra_etale_of_cast_eq_zero (a : R) (hp : (p : R) = 0) :
    Algebra.Etale R (RootAlgebra p a) := by
  let t : RootAlgebra p a := AdjoinRoot.mk (poly p a) 1
  let S := Localization.Away t
  have hu : IsUnit t := (isUnit_one : IsUnit (1 : R[X])).map (AdjoinRoot.mk _)
  have : Algebra.Etale R S :=
    Algebra.Etale.of_equiv (standardPairOfCastEqZero p a hp).equivAwayAdjoinRoot
  exact Algebra.Etale.of_equiv
    ((IsLocalization.atUnit (RootAlgebra p a) S t hu).symm.restrictScalars R)

instance rootAlgebra_etale [CharP R p] (a : R) : Algebra.Etale R (RootAlgebra p a) :=
  rootAlgebra_etale_of_cast_eq_zero p a (CharP.cast_eq_zero R p)

instance rootAlgebra_faithfulSMul (a : R) : FaithfulSMul R (RootAlgebra p a) := by
  rcases subsingleton_or_nontrivial R with h | h
  · let := h
    constructor
    intro r s _
    exact Subsingleton.elim r s
  · let := h
    apply AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (poly_monic p a)
    rw [degree_poly]
    exact_mod_cast (Fact.out : p.Prime).pos

/-- The original quotient map covers the whole prime spectrum, including for the zero ring. -/
lemma spectrum_surjective (a : R) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R (RootAlgebra p a))) := by
  let := AdjoinRoot.isIntegral_of_monic (poly_monic p a)
  exact Algebra.IsIntegral.comap_surjective R (RootAlgebra p a)

end Algebra.ArtinSchreier
