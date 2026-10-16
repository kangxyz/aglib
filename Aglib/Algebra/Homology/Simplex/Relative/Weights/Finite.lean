/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Contraction
public import Aglib.Algebra.Homology.Simplex.Relative.Empty
public import Aglib.Algebra.Homology.Simplex.Relative.Finite
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Homology
public import Aglib.LinearAlgebra.DFinsupp.Subtype
public import Aglib.RingTheory.MvPolynomial.CoordinateExponents
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Finite free homology of the original Laurent tuple complex

Only empty and full negative support can contribute actual homology. Their
original fixed-degree exponent types are finite. Restriction of the actual
weight homology sum to those endpoints therefore proves finite generation;
the relative-simplex calculation also proves that every summand is free.
For `Fin (n + 1)` the original homology vanishes away from degrees zero and
`n`, retaining both possible contributions when `n = 0`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v}

theorem coordinateNegativeSupport_eq_empty_iff (e : ι →₀ ℤ) :
    coordinateNegativeSupport e = ∅ ↔ ∀ i, 0 ≤ e i := by
  simp only [Set.eq_empty_iff_forall_notMem, coordinateNegativeSupport,
    Set.mem_ofPred_eq, not_lt]

theorem coordinateNegativeSupport_eq_univ_iff (e : ι →₀ ℤ) :
    coordinateNegativeSupport e = Set.univ ↔ ∀ i, e i < 0 :=
  Set.eq_univ_iff_forall

/-- Empty negative support is the native nonnegative integer-exponent fiber. -/
def coordinateEmptyWeightEquiv (d : ℤ) :
    {e : coordinateLaurentWeight (ι := ι) d // coordinateNegativeSupport e.val = ∅} ≃
      coordinateNonnegativeDegreeExponents (ι := ι) d where
  toFun e := ⟨e.val.val, ⟨e.val.property,
    (coordinateNegativeSupport_eq_empty_iff e.val.val).mp e.property⟩⟩
  invFun e := ⟨⟨e.val, e.property.1⟩,
    (coordinateNegativeSupport_eq_empty_iff e.val).mpr e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full negative support is the native all-negative coordinate exponent fiber. -/
def coordinateFullWeightEquiv [Fintype ι] (d : ℤ) :
    {e : coordinateLaurentWeight (ι := ι) d // coordinateNegativeSupport e.val = Set.univ} ≃
      coordinateNegativeDegreeExponents (ι := ι) d where
  toFun e := ⟨⟨e.val.val, by intro i hi; exact (hi (Finset.mem_univ i)).elim⟩, ⟨e.val.property,
    (coordinateNegativeSupport_eq_univ_iff e.val.val).mp e.property⟩⟩
  invFun e := ⟨⟨e.val.val, e.property.1⟩,
    (coordinateNegativeSupport_eq_univ_iff e.val.val).mpr e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Original weights with empty or full negative support, retaining both
endpoints in projective dimension zero. -/
abbrev coordinateLaurentEndpointWeight (d : ℤ) :=
  {e : coordinateLaurentWeight (ι := ι) d //
    coordinateNegativeSupport e.val = ∅ ∨ coordinateNegativeSupport e.val = Set.univ}

instance [Finite ι] (d : ℤ) : Finite (coordinateLaurentEndpointWeight (ι := ι) d) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : Finite {e : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport e.val = ∅} :=
    Finite.of_equiv _ (coordinateEmptyWeightEquiv d).symm
  let : Finite {e : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport e.val = Set.univ} :=
    Finite.of_equiv _ (coordinateFullWeightEquiv d).symm
  let f : {e : coordinateLaurentWeight (ι := ι) d // coordinateNegativeSupport e.val = ∅} ⊕
      {e : coordinateLaurentWeight (ι := ι) d // coordinateNegativeSupport e.val = Set.univ} →
        coordinateLaurentEndpointWeight (ι := ι) d :=
    Sum.elim (fun e => ⟨e.val, Or.inl e.property⟩) (fun e => ⟨e.val, Or.inr e.property⟩)
  apply Finite.of_surjective f
  rintro ⟨e, he | he⟩
  · exact ⟨Sum.inl ⟨e, he⟩, rfl⟩
  · exact ⟨Sum.inr ⟨e, he⟩, rfl⟩

variable (R : Type u) [CommRing R]

/-- Every original proper-nonempty-support weight has zero native homology. -/
theorem coordinateLaurentWeightHomology_isZero_of_not_endpoint {d : ℤ}
    (e : coordinateLaurentWeight (ι := ι) d)
    (he : ¬ (coordinateNegativeSupport e.val = ∅ ∨
      coordinateNegativeSupport e.val = Set.univ)) (q : ℕ) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) := by
  have hE : coordinateNegativeSupport e.val ≠ ∅ := fun h => he (Or.inl h)
  have hF : coordinateNegativeSupport e.val ≠ Set.univ := fun h => he (Or.inr h)
  obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem _).mp hF
  exact (RelativeSimplex.acyclic_of_nonempty_of_not_mem (R := R) j hj
    (Set.nonempty_iff_ne_empty.mpr hE) q).isZero_homology

/-- The original homology sum restricted to the finite endpoint weights.
The map is literally the existing dependent-sum coefficient restriction. -/
def coordinateLaurentTupleHomologyEndpointEquiv [Finite ι] (d : ℤ) (q : ℕ) :
    (coordinateLaurentTupleComplex (ι := ι) R d).homology q ≃ₗ[R]
      (Π₀ e : coordinateLaurentEndpointWeight (ι := ι) d,
        (RelativeSimplex.complex R (coordinateNegativeSupport e.val.val)).homology q) := by
  classical
  exact (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q).trans
    (DFinsupp.subtypeDomainLinearEquiv (R := R)
      (fun e : coordinateLaurentWeight (ι := ι) d =>
        coordinateNegativeSupport e.val = ∅ ∨ coordinateNegativeSupport e.val = Set.univ)
      (fun e he => ModuleCat.subsingleton_of_isZero
        (coordinateLaurentWeightHomology_isZero_of_not_endpoint R e he q)))

/-- Each original weight on `n + 1` vertices has finite free native homology,
over every commutative ring. -/
theorem coordinateLaurentWeightHomology_finite_free (n : ℕ) (d : ℤ) (q : ℕ)
    (e : coordinateLaurentWeight (ι := Fin (n + 1)) d) :
    Module.Finite R ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) ∧
      Module.Free R ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport e.val = ∅
  · rw [hE]
    cases q with
    | zero =>
      exact ⟨Module.Finite.equiv (RelativeSimplex.emptySupportHomologyZeroLinearEquiv
        (R := R) (0 : Fin (n + 1)) |>.symm), Module.Free.of_equiv
          (RelativeSimplex.emptySupportHomologyZeroLinearEquiv (R := R)
            (0 : Fin (n + 1)) |>.symm)⟩
    | succ q =>
      let := ModuleCat.subsingleton_of_isZero
        (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set (Fin (n + 1))))
          (0 : Fin (n + 1)) (by simp) q).isZero_homology
      exact ⟨inferInstance, inferInstance⟩
  · by_cases hF : coordinateNegativeSupport e.val = Set.univ
    · rw [hF]
      by_cases hq : q = n
      · subst q
        exact ⟨Module.Finite.equiv (RelativeSimplex.fullSupportTopLinearEquiv R n).symm,
          Module.Free.of_equiv (RelativeSimplex.fullSupportTopLinearEquiv R n).symm⟩
      · let := ModuleCat.subsingleton_of_isZero
          (RelativeSimplex.fullSupport_isZero_homology_of_ne (R := R) n q hq)
        exact ⟨inferInstance, inferInstance⟩
    · let := ModuleCat.subsingleton_of_isZero
        (coordinateLaurentWeightHomology_isZero_of_not_endpoint R e (by tauto) q)
      exact ⟨inferInstance, inferInstance⟩

/-- Original raw Laurent tuple homology is free in every degree. -/
instance coordinateLaurentTupleHomology_free (n : ℕ) (d : ℤ) (q : ℕ) :
    Module.Free R ((coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology q) := by
  let : ∀ e : coordinateLaurentWeight (ι := Fin (n + 1)) d,
      Module.Free R ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) :=
    fun e => (coordinateLaurentWeightHomology_finite_free R n d q e).2
  exact Module.Free.of_equiv
    (coordinateLaurentTupleHomologyWeightsEquiv (ι := Fin (n + 1)) R d q).symm

/-- The original raw Laurent tuple homology is finite over the scalar ring,
because only its actual finite endpoint weight set can contribute. -/
instance coordinateLaurentTupleHomology_finite (n : ℕ) (d : ℤ) (q : ℕ) :
    Module.Finite R ((coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology q) := by
  let : ∀ e : coordinateLaurentEndpointWeight (ι := Fin (n + 1)) d,
      Module.Finite R
        ((RelativeSimplex.complex R (coordinateNegativeSupport e.val.val)).homology q) :=
    fun e => (coordinateLaurentWeightHomology_finite_free R n d q e.val).1
  exact Module.Finite.equiv
    (coordinateLaurentTupleHomologyEndpointEquiv (ι := Fin (n + 1)) R d q).symm

/-- Each original weight vanishes away from degree zero and the top degree. -/
theorem coordinateLaurentWeightHomology_isZero_of_ne_endpoints (n : ℕ) (d : ℤ) (q : ℕ)
    (hq0 : q ≠ 0) (hqn : q ≠ n)
    (e : coordinateLaurentWeight (ι := Fin (n + 1)) d) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport e.val = ∅
  · rw [hE]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    exact (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set (Fin (n + 1))))
      (0 : Fin (n + 1)) (by simp) q).isZero_homology
  · by_cases hF : coordinateNegativeSupport e.val = Set.univ
    · rw [hF]
      exact RelativeSimplex.fullSupport_isZero_homology_of_ne n q hqn
    · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R e (by tauto) q

/-- Vanishing of the unchanged raw Laurent homology away from the two
possible endpoint degrees. -/
theorem coordinateLaurentTupleHomology_isZero_of_ne_endpoints (n : ℕ) (d : ℤ) (q : ℕ)
    (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero ((coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (coordinateLaurentTupleHomologyWeightsEquiv (ι := Fin (n + 1)) R d q).injective
  ext e
  exact (ModuleCat.subsingleton_of_isZero
    (coordinateLaurentWeightHomology_isZero_of_ne_endpoints R n d q hq0 hqn e)).elim _ _

/-- Above the all-negative residue degree, every original weight has zero
positive homology. This is the sharp twist-vanishing bound `d ≥ -n`. -/
theorem coordinateLaurentWeightHomology_isZero_of_neg_le_degree (n : ℕ) (d : ℤ) (q : ℕ)
    (hd : -(n : ℤ) ≤ d) (hq : q ≠ 0)
    (e : coordinateLaurentWeight (ι := Fin (n + 1)) d) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport e.val = ∅
  · rw [hE]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set (Fin (n + 1))))
      (0 : Fin (n + 1)) (by simp) q).isZero_homology
  · by_cases hF : coordinateNegativeSupport e.val = Set.univ
    · have hz := coordinateNegativeDegreeExponents_isEmpty (ι := Fin (n + 1)) d (by
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
        omega)
      exact (hz.false (coordinateFullWeightEquiv d ⟨e, hF⟩)).elim
    · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R e (by tauto) q

/-- The unchanged Laurent tuple complex has no positive homology for
`d ≥ -n`, over every commutative ring and including projective dimension zero. -/
theorem coordinateLaurentTupleHomology_isZero_of_neg_le_degree (n : ℕ) (d : ℤ) (q : ℕ)
    (hd : -(n : ℤ) ≤ d) (hq : q ≠ 0) :
    IsZero ((coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (coordinateLaurentTupleHomologyWeightsEquiv (ι := Fin (n + 1)) R d q).injective
  ext e
  exact (ModuleCat.subsingleton_of_isZero
    (coordinateLaurentWeightHomology_isZero_of_neg_le_degree R n d q hd hq e)).elim _ _

end MvPolynomial
