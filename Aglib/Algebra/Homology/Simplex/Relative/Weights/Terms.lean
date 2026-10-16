/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Exchange
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Laurent
public import Aglib.Algebra.Homology.Simplex.Relative.Basic

/-!
# Actual weight coefficients of the original Laurent tuple modules

The unrestricted integer exponent vectors of degree `d` are the weights. A
weight is allowed on a tuple exactly when every negative coordinate occurs
in that tuple. The native graded monomial basis and the proved finite-row
interchange identify the original tuple Laurent module with the dependent
finitely supported sum of actual relative-simplex cochain modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace MvPolynomial

universe u v

variable {ι : Type v} {n : ℕ}

/-- The unrestricted original integer exponents in the indicated total degree. -/
abbrev coordinateLaurentWeight (d : ℤ) := {e : ι →₀ ℤ // e.degree = d}

/-- The exact set of negative coordinates of an original integer exponent. -/
def coordinateNegativeSupport (e : ι →₀ ℤ) : Set ι := {i | e i < 0}

/-- A tuple permits exactly those weights whose negative coordinates occur in it. -/
abbrev coordinateWeightAllowed {d : ℤ} (a : Fin (n + 1) → ι)
    (e : coordinateLaurentWeight (ι := ι) d) := coordinateNegativeSupport e.val ⊆ Set.range a

theorem coordinateExponentAllowed_iff_negativeSupport (a : Fin (n + 1) → ι) (e : ι →₀ ℤ) :
    e ∈ coordinateExponentMonoid (coordinateTupleSet a) ↔
      coordinateNegativeSupport e ⊆ Set.range a := by
  change (∀ i, i ∉ coordinateTupleSet a → 0 ≤ e i) ↔ _
  constructor
  · intro h i hi
    by_contra hn
    have hz := h i (fun hmem => hn ((mem_coordinateTupleSet a i).mp hmem))
    change e i < 0 at hi
    omega
  · intro h i hi
    by_contra hn
    have hneg : i ∈ coordinateNegativeSupport e := by
      change e i < 0
      omega
    exact hi ((mem_coordinateTupleSet a i).mpr (h hneg))

/-- The same original exponent as an element of the native tuple localization monoid. -/
def coordinateWeightExponent {d : ℤ} (a : Fin (n + 1) → ι)
    (e : coordinateLaurentWeight (ι := ι) d) (he : coordinateWeightAllowed a e) :
    coordinateExponentMonoid (coordinateTupleSet a) :=
  ⟨e.val, (coordinateExponentAllowed_iff_negativeSupport a e.val).mpr he⟩

/-- Original local graded exponent indices are exactly the allowed unrestricted weights. -/
def coordinateTupleWeightEquiv (d : ℤ) (a : Fin (n + 1) → ι) :
    {e : coordinateExponentMonoid (coordinateTupleSet a) //
      coordinateDegree (coordinateTupleSet a) e = d} ≃
      {e : coordinateLaurentWeight (ι := ι) d // coordinateWeightAllowed a e} where
  toFun e := ⟨⟨e.val.val, e.property⟩,
    (coordinateExponentAllowed_iff_negativeSupport a e.val.val).mp e.val.property⟩
  invFun e := ⟨coordinateWeightExponent a e.val e.property, e.val.property⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

variable (R : Type u) [CommRing R]

/-- Native graded coefficients, indexed by the actual allowed global weights. -/
def coordinateLaurentTupleCoefficients (d : ℤ) (a : Fin (n + 1) → ι) :
    coordinateGrading R (coordinateTupleSet a) d ≃ₗ[R]
      ({e : coordinateLaurentWeight (ι := ι) d // coordinateWeightAllowed a e} →₀ R) :=
  (coordinateGradeEquivFinsupp R (coordinateTupleSet a) d).trans
    (Finsupp.domLCongr (coordinateTupleWeightEquiv d a))

@[simp]
theorem coordinateLaurentTupleCoefficients_apply (d : ℤ) (a : Fin (n + 1) → ι)
    (x : coordinateGrading R (coordinateTupleSet a) d)
    (e : {e : coordinateLaurentWeight (ι := ι) d // coordinateWeightAllowed a e}) :
    coordinateLaurentTupleCoefficients R d a x e =
      x.val.coeff (coordinateWeightExponent a e.val e.property) := by
  simp [coordinateLaurentTupleCoefficients, coordinateTupleWeightEquiv,
    Finsupp.equivMapDomain_apply, coordinateWeightExponent]

/-- Native graded monomial coordinates retain actual single Laurent monomials. -/
theorem coordinateGradeEquivFinsupp_symm_single (s : Finset ι) (d : ℤ)
    (e : {e : coordinateExponentMonoid s // coordinateDegree s e = d}) (r : R) :
    ((coordinateGradeEquivFinsupp R s d).symm (Finsupp.single e r)).val =
      AddMonoidAlgebra.single e.val r := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single e r)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single, AddMonoidAlgebra.ofCoeff_single]

/-- The proved finite product / weight-sum exchange on the original raw Laurent terms. -/
def coordinateLaurentTupleWeightsEquiv [Finite ι] (d : ℤ) (n : ℕ) :
    coordinateLaurentTupleCochains (ι := ι) R d n ≃ₗ[R]
      (Π₀ e : coordinateLaurentWeight (ι := ι) d,
        AlgebraicTopology.RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n) :=
  (LinearEquiv.piCongrRight fun a => coordinateLaurentTupleCoefficients R d a).trans
    (Finsupp.piSubtypeLEquivDFinsupp (M := R) R
      (fun a : Fin (n + 1) → ι => fun e : coordinateLaurentWeight (ι := ι) d =>
        coordinateWeightAllowed a e))

/-- The actual exchanged component is the unchanged original Laurent coefficient. -/
@[simp]
theorem coordinateLaurentTupleWeightsEquiv_apply [Finite ι] (d : ℤ) (n : ℕ)
    (x : coordinateLaurentTupleCochains (ι := ι) R d n)
    (e : coordinateLaurentWeight (ι := ι) d)
    (a : AlgebraicTopology.RelativeSimplex.Tuple (coordinateNegativeSupport e.val) n) :
    coordinateLaurentTupleWeightsEquiv (ι := ι) R d n x e a =
      (x a.val).val.coeff (coordinateWeightExponent a.val e a.property) := by
  simp only [coordinateLaurentTupleWeightsEquiv, LinearEquiv.trans_apply,
    Finsupp.piSubtypeLEquivDFinsupp_apply]
  exact coordinateLaurentTupleCoefficients_apply R d a.val (x a.val) ⟨e, a.property⟩

/-- The inverse exchange retains each coefficient at its original permitted weight. -/
@[simp]
theorem coordinateLaurentTupleWeightsEquiv_symm_coeff [Finite ι] (d : ℤ) (n : ℕ)
    (x : Π₀ e : coordinateLaurentWeight (ι := ι) d,
      AlgebraicTopology.RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n)
    (e : coordinateLaurentWeight (ι := ι) d) (a : Fin (n + 1) → ι)
    (ha : coordinateWeightAllowed a e) :
    (((coordinateLaurentTupleWeightsEquiv (ι := ι) R d n).symm x) a).val.coeff
      (coordinateWeightExponent a e ha) = x e ⟨a, ha⟩ := by
  have h := coordinateLaurentTupleWeightsEquiv_apply R d n
    ((coordinateLaurentTupleWeightsEquiv (ι := ι) R d n).symm x) e ⟨a, ha⟩
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end MvPolynomial
