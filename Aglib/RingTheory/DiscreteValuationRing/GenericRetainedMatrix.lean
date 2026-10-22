/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.Matrix.RetainedAdjugate
public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Aglib.RingTheory.DiscreteValuationRing.ParameterMap

/-! # The actual generic coordinate matrix and its retained minor

The matrix lives in the native parameter DVR. Both invertibility and the unit
normalization factor follow from the actual parameter residue field, not from
an independently chosen specialization.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial Matrix

namespace ParameterLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : Type*) [Fintype n] [DecidableEq n] (p : R) [Fact (Irreducible p)]

/-- The whole coordinate matrix in the actual coefficient parameter DVR. -/
def genericMatrix : Matrix n n (Ring R (n × n) p) :=
  (algebraMap (MvPolynomial (n × n) R) (Ring R (n × n) p)).mapMatrix
    (mvPolynomialX n n R)

omit [Fintype n] [DecidableEq n] in
/-- A polynomial nonzero modulo the original maximal ideal becomes a unit in
its actual parameter DVR. -/
theorem isUnit_polynomial_of_residue_ne_zero (H : MvPolynomial (n × n) R)
    (hH : MvPolynomial.map (residue R) H ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (n × n) R) (Ring R (n × n) p) H) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  intro hz
  have he := congrArg (residueFieldAlgEquiv R (n × n) p) hz
  rw [residueFieldAlgEquiv_polynomial, map_zero] at he
  exact hH ((FaithfulSMul.algebraMap_injective
    (MvPolynomial (n × n) (ResidueField R))
    (FractionRing (MvPolynomial (n × n) (ResidueField R))))
      (he.trans (map_zero _).symm))

/-- The actual whole generic matrix is invertible over the parameter DVR. -/
theorem isUnit_det_genericMatrix : IsUnit (genericMatrix R n p).det := by
  change IsUnit ((algebraMap (MvPolynomial (n × n) R) (Ring R (n × n) p)).mapMatrix
    (mvPolynomialX n n R)).det
  rw [← RingHom.map_det]
  apply isUnit_polynomial_of_residue_ne_zero
  have he : MvPolynomial.map (residue R) (mvPolynomialX n n R).det =
      (mvPolynomialX n n (ResidueField R)).det := by
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    simp [mvPolynomialX]
  rw [he]
  exact det_mvPolynomialX_ne_zero n (ResidueField R)

/-- The genuine retained adjugate minor of the same matrix is the original
minimum-order minor times an actual unit of the target parameter DVR. -/
theorem exists_generic_retained_minor_unit {c : ℕ} (A : Matrix (Fin c) n R)
    (δ : R) (hδ : δ ≠ 0) (hI : A.minorIdeal c = Ideal.span {δ})
    (cols : Fin c → n) (hcols : (A.submatrix _root_.id cols).det = δ)
    (b : Fin c ↪ n) :
    ∃ h : Ring R (n × n) p, IsUnit h ∧
      (((A.map (algebraMap R (Ring R (n × n) p))) *
        (genericMatrix R n p).adjugate).submatrix _root_.id b).det =
          algebraMap R (Ring R (n × n) p) δ * h := by
  obtain ⟨H, hH, hH₀⟩ := exists_normalized_retained_adjugate A δ hδ hI cols hcols b
  let ℓ := algebraMap (MvPolynomial (n × n) R) (Ring R (n × n) p)
  refine ⟨ℓ H, isUnit_polynomial_of_residue_ne_zero R n p H hH₀, ?_⟩
  have hcoeff : (A.map (C : R →+* MvPolynomial (n × n) R)).map ℓ =
      A.map (algebraMap R (Ring R (n × n) p)) := by
    ext i j
    exact IsScalarTower.algebraMap_apply R (MvPolynomial (n × n) R)
      (Ring R (n × n) p) (A i j)
  have hadj : ((mvPolynomialX n n R).adjugate).map ℓ =
      (genericMatrix R n p).adjugate := ℓ.map_adjugate _
  have hmat : ((A.map (C : R →+* MvPolynomial (n × n) R)) *
      (mvPolynomialX n n R).adjugate).map ℓ =
      A.map (algebraMap R (Ring R (n × n) p)) * (genericMatrix R n p).adjugate := by
    rw [Matrix.map_mul, hcoeff, hadj]
  have hh := congrArg ℓ hH
  rw [map_mul, RingHom.map_det] at hh
  have hc : ℓ (C δ) = algebraMap R (Ring R (n × n) p) δ :=
    IsScalarTower.algebraMap_apply R (MvPolynomial (n × n) R) (Ring R (n × n) p) δ
  rw [hc] at hh
  change (((((A.map C) * (mvPolynomialX n n R).adjugate).submatrix _root_.id b).map ℓ).det)
    = _ at hh
  rw [← Matrix.submatrix_map, hmat] at hh
  exact hh

/-- The source and target generic matrices are literally the images of the same
variables under the actual coefficient-change map. -/
theorem parameterMap_genericMatrix
    (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [Fact (Irreducible (algebraMap R S p))] :
    (genericMatrix R n p).map (parameterMap R S (n × n) p) =
      genericMatrix S n (algebraMap R S p) := by
  ext i j
  change parameterMap R S (n × n) p
      (algebraMap (MvPolynomial (n × n) R) (Ring R (n × n) p) (X (i, j))) =
    algebraMap (MvPolynomial (n × n) S)
      (Ring S (n × n) (algebraMap R S p)) (X (i, j))
  exact parameterMap_X R S (n × n) p (i, j)

end ParameterLocalization
