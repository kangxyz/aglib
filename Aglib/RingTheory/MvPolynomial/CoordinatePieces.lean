/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.RingTheory.MvPolynomial.CoordinateExponents
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Native finite free monomial pieces for the Laurent residue pairing

The polynomial piece is the original `homogeneousSubmodule`; the negative
Laurent piece is the native `AddMonoidAlgebra.supported` submodule. Their
displayed Finsupp comparisons and bases retain the original monomials and
coefficients, with finite exponent index sets over every commutative ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators
open Module

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The exact degree specialization of complementary polynomial and negative
Laurent monomial indices. -/
def coordinateHomogeneousNegativeExponentEquiv (m : ℕ) :
    {a : ι →₀ ℕ // a.degree = m} ≃
      coordinateNegativeDegreeExponents (ι := ι) (-(m : ℤ) - (Fintype.card ι : ℤ)) :=
  (show {a : ι →₀ ℕ // a.degree = m} ≃
      {a : ι →₀ ℕ // (a.degree : ℤ) = -(-(m : ℤ) - (Fintype.card ι : ℤ)) -
        (Fintype.card ι : ℤ)} from {
    toFun a := ⟨a.val, by have := a.property; omega⟩
    invFun a := ⟨a.val, by have := a.property; omega⟩
    left_inv _ := rfl
    right_inv _ := rfl }).trans (coordinateNegativeDegreeExponentEquiv _)

@[simp]
theorem coordinateHomogeneousNegativeExponentEquiv_val (m : ℕ)
    (a : {a : ι →₀ ℕ // a.degree = m}) :
    (coordinateHomogeneousNegativeExponentEquiv m a).val = coordinateNegativeComplement a.val := rfl

/-- The two actual monomial exponents add to the residue exponent. -/
theorem coordinateExponentOfNat_add_negativeComplement (a : ι →₀ ℕ) :
    coordinateExponentOfNat Finset.univ a + coordinateNegativeComplement a =
      coordinateNegativeProductExponent Finset.univ := by
  apply Subtype.ext
  ext i
  simp [coordinateNegativeComplement]

variable (R : Type*) [CommRing R]

/-- The native submodule on all-negative degree-`d` Laurent monomials. -/
abbrev coordinateNegativePiece (d : ℤ) :
    Submodule R (coordinateLaurentAlgebra R (Finset.univ : Finset ι)) :=
  AddMonoidAlgebra.supported R R {e : coordinateExponentMonoid (Finset.univ : Finset ι) |
    coordinateDegree Finset.univ e = d ∧ ∀ i, e.val i < 0}

/-- The native coefficient-preserving Finsupp presentation of the negative piece. -/
def coordinateNegativePieceEquivFinsupp (d : ℤ) :
    coordinateNegativePiece (ι := ι) R d ≃ₗ[R]
      (coordinateNegativeDegreeExponents (ι := ι) d →₀ R) :=
  AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) _

@[simp]
theorem coordinateNegativePieceEquivFinsupp_apply (d : ℤ)
    (g : coordinateNegativePiece (ι := ι) R d) (e : coordinateNegativeDegreeExponents (ι := ι) d) :
    coordinateNegativePieceEquivFinsupp R d g e = g.val.coeff e.val := rfl

omit [Fintype ι] in
/-- The native coefficient-preserving Finsupp presentation of the original homogeneous piece. -/
def homogeneousPieceEquivFinsupp (m : ℕ) :
    homogeneousSubmodule ι R m ≃ₗ[R] ({a : ι →₀ ℕ // a.degree = m} →₀ R) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported ι R m)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) _)

omit [Fintype ι] in
@[simp]
theorem homogeneousPieceEquivFinsupp_apply (m : ℕ)
    (p : homogeneousSubmodule ι R m) (a : {a : ι →₀ ℕ // a.degree = m}) :
    homogeneousPieceEquivFinsupp R m p a = p.val.coeff a.val := rfl

/-- The displayed native monomial basis of the all-negative Laurent piece. -/
def coordinateNegativePieceBasis (d : ℤ) :
    Basis (coordinateNegativeDegreeExponents (ι := ι) d) R (coordinateNegativePiece (ι := ι) R d) :=
  Finsupp.basisSingleOne.map (coordinateNegativePieceEquivFinsupp R d).symm

omit [Fintype ι] in
/-- The displayed native monomial basis of the original polynomial homogeneous piece. -/
def homogeneousPieceBasis (m : ℕ) :
    Basis {a : ι →₀ ℕ // a.degree = m} R (homogeneousSubmodule ι R m) :=
  Finsupp.basisSingleOne.map (homogeneousPieceEquivFinsupp R m).symm

@[simp]
theorem coordinateNegativePieceBasis_val (d : ℤ)
    (e : coordinateNegativeDegreeExponents (ι := ι) d) :
    (coordinateNegativePieceBasis R d e).val = AddMonoidAlgebra.single e.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single e (1 : R))).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single, AddMonoidAlgebra.ofCoeff_single]

omit [Fintype ι] in
@[simp]
theorem homogeneousPieceBasis_val (m : ℕ) (a : {a : ι →₀ ℕ // a.degree = m}) :
    (homogeneousPieceBasis R m a).val = monomial a.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single a (1 : R))).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

instance (d : ℤ) : Module.Free R (coordinateNegativePiece (ι := ι) R d) :=
  Module.Free.of_basis (coordinateNegativePieceBasis R d)

instance (d : ℤ) : Module.Finite R (coordinateNegativePiece (ι := ι) R d) :=
  Module.Finite.of_basis (coordinateNegativePieceBasis R d)

omit [Fintype ι] in
instance (m : ℕ) : Module.Free R (homogeneousSubmodule ι R m) :=
  Module.Free.of_basis (homogeneousPieceBasis R m)

omit [Fintype ι] in
instance [Finite ι] (m : ℕ) : Module.Finite R (homogeneousSubmodule ι R m) := by
  have : Finite {a : ι →₀ ℕ // a.degree = m} := (Finsupp.finite_of_degree_eq m).to_subtype
  exact Module.Finite.of_basis (homogeneousPieceBasis R m)

/-- Above the residue degree the actual negative Laurent submodule is zero. -/
theorem coordinateNegativePiece_eq_bot (d : ℤ) (hd : -(Fintype.card ι : ℤ) < d) :
    coordinateNegativePiece (ι := ι) R d = ⊥ := by
  have := coordinateNegativeDegreeExponents_isEmpty (ι := ι) d hd
  have : Subsingleton (coordinateNegativePiece (ι := ι) R d) :=
    (coordinateNegativePieceEquivFinsupp R d).injective.subsingleton
  apply le_antisymm
  · intro g hg
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨g, hg⟩ : coordinateNegativePiece (ι := ι) R d) 0)
  · exact bot_le

end MvPolynomial
