/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.LaurentPairing.Pieces
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The native perfect Laurent residue pairing

The pairing is the actual coefficient of the all-minus-one monomial in the
product of an original homogeneous polynomial and an original all-negative
Laurent polynomial. Complementary monomial exponents give dual finite bases,
so this literal pairing is perfect over every commutative coefficient ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Module
open scoped BigOperators

namespace MvPolynomial

variable {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- The actual residue coefficient of a product, on the original two native
monomial submodules. -/
def coordinateLaurentResiduePairing (m : ℕ) :
    homogeneousSubmodule ι R m →ₗ[R]
      coordinateNegativePiece (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ)) →ₗ[R] R where
  toFun p := {
    toFun g := ((toCoordinateLaurent R Finset.univ p.val) * g.val).coeff
      (coordinateNegativeProductExponent Finset.univ)
    map_add' g h := by simp [mul_add]
    map_smul' r g := by simp }
  map_add' p q := by
    ext g
    simp [add_mul]
  map_smul' r p := by
    ext g
    simp

/-- The pairing retains its defining original polynomial inclusion,
Laurent multiplication and actual residue coefficient. -/
@[simp]
theorem coordinateLaurentResiduePairing_apply (m : ℕ) (p : homogeneousSubmodule ι R m)
    (g : coordinateNegativePiece (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ))) :
    coordinateLaurentResiduePairing R m p g =
      ((toCoordinateLaurent R Finset.univ p.val) * g.val).coeff
        (coordinateNegativeProductExponent Finset.univ) := rfl

open Classical in
/-- The original residue of two monomial basis vectors is the Kronecker symbol
for the literal exponent complement `βᵢ = -1 - αᵢ`. -/
theorem coordinateLaurentResiduePairing_basis (m : ℕ)
    (a : {a : ι →₀ ℕ // a.degree = m})
    (e : coordinateNegativeDegreeExponents (ι := ι) (-(m : ℤ) - (Fintype.card ι : ℤ))) :
    coordinateLaurentResiduePairing R m (homogeneousPieceBasis R m a)
        (coordinateNegativePieceBasis R _ e) =
      if e = coordinateHomogeneousNegativeExponentEquiv m a then 1 else 0 := by
  classical
  rw [coordinateLaurentResiduePairing_apply, homogeneousPieceBasis_val,
    coordinateNegativePieceBasis_val, toCoordinateLaurent_monomial,
    AddMonoidAlgebra.single_mul_single]
  have he : coordinateExponentOfNat Finset.univ a.val + e.val =
        coordinateNegativeProductExponent Finset.univ ↔
      e = coordinateHomogeneousNegativeExponentEquiv m a := by
    constructor
    · intro h
      apply Subtype.ext
      exact add_left_cancel
        (h.trans (coordinateExponentOfNat_add_negativeComplement a.val).symm)
    · intro h
      subst e
      exact coordinateExponentOfNat_add_negativeComplement a.val
  simp only [mul_one, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, he]

/-- The literal residue coefficient pairing is a native perfect pairing, with
bijective maps to both linear duals over the arbitrary commutative ring. -/
instance coordinateLaurentResiduePairing_isPerfPair (m : ℕ) :
    (coordinateLaurentResiduePairing (ι := ι) R m).IsPerfPair := by
  classical
  let P := homogeneousPieceBasis (ι := ι) R m
  let Q := coordinateNegativePieceBasis (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ))
  let E := P.equiv Q.dualBasis (coordinateHomogeneousNegativeExponentEquiv m)
  have hE : E.toLinearMap = coordinateLaurentResiduePairing R m := by
    apply P.ext
    intro a
    apply Q.ext
    intro e
    change E (P a) (Q e) = _
    simp only [E, Basis.equiv_apply, Basis.dualBasis_apply_self]
    exact (coordinateLaurentResiduePairing_basis R m a e).symm
  apply LinearMap.IsPerfPair.of_bijective
  rw [← hE]
  exact E.bijective

/-- The native perfect-pairing equivalence from original homogeneous polynomials
to the linear dual of the actual negative Laurent piece. -/
def coordinateLaurentResidueDuality (m : ℕ) :
    homogeneousSubmodule ι R m ≃ₗ[R]
      Dual R (coordinateNegativePiece (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ))) :=
  (coordinateLaurentResiduePairing R m).toPerfPair

@[simp]
theorem coordinateLaurentResidueDuality_apply (m : ℕ) (p : homogeneousSubmodule ι R m)
    (g : coordinateNegativePiece (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ))) :
    coordinateLaurentResidueDuality R m p g =
      ((toCoordinateLaurent R Finset.univ p.val) * g.val).coeff
        (coordinateNegativeProductExponent Finset.univ) := rfl

end MvPolynomial
