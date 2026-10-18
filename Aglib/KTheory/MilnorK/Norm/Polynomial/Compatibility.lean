/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Basic
public import Aglib.KTheory.MilnorK.Residue.Compatibility
public import Aglib.KTheory.MilnorK.K3.PolynomialNorm

/-!
# The degree-two polynomial norm agrees with the original norm

The degree-two and degree-three presentation equivalences intertwine every
actual finite polynomial residue and the actual infinity residue. Surjectivity
of the genuine total finite residue map then compares the two total norms on
every residue vector and hence every polynomial component on every class.
No restriction to root or constant symbols and no characteristic hypothesis
is used. Independence from polynomial presentations is not asserted.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial

variable {k : Type*} [Field k]

/-- Every finite polynomial residue agrees with the original degree-three residue. -/
theorem twoEquiv_residueAt (p : k[X]) [Fact (Irreducible p)]
    (x : K (RatFunc k) 3) :
    twoEquiv (AdjoinRoot p) (PolynomialResidue.residueAt p 2 x) =
      MilnorK.K3.PolynomialResidue.residueAt p (threeEquiv (RatFunc k) x) := by
  simp only [PolynomialResidue.residueAt, MilnorK.K3.PolynomialResidue.residueAt,
    LinearMap.comp_apply, twoEquiv_map, twoEquiv_residue_two,
    MilnorK.K3.DVR.residue_eq (Polynomial.LocalResidue.irreducible_polynomial p),
    MilnorK.K3.DVR.residueWithUniformizer]

/-- The full infinity residue agrees under the same presentation equivalences. -/
theorem twoEquiv_infinityResidue (x : K (RatFunc k) 3) :
    twoEquiv k (InfinityResidue.residue k 2 x) =
      MilnorK.K3.InfinityResidue.residue k (threeEquiv (RatFunc k) x) := by
  simp only [InfinityResidue.residue, MilnorK.K3.InfinityResidue.residue,
    LinearMap.comp_apply, twoEquiv_map, twoEquiv_residueAt]
  rw [threeEquiv_map]
  rfl

namespace PolynomialNorm

open PolynomialResidue

/-- Apply the actual degree-two equivalence to each finite residue coordinate. -/
def residueTwoMap :
    (Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) 2) →ₗ[ℤ]
      Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val) :=
  DFinsupp.mapRange.linearMap fun p => (twoEquiv (AdjoinRoot p.val)).toLinearMap

@[simp] theorem residueTwoMap_apply
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) 2) (p : MonicIrreducible k) :
    residueTwoMap y p = twoEquiv (AdjoinRoot p.val) (y p) := rfl

@[simp] theorem residueTwoMap_single [DecidableEq (MonicIrreducible k)]
    (p : MonicIrreducible k) (y : K (AdjoinRoot p.val) 2) :
    residueTwoMap (DFinsupp.single p y) =
      DFinsupp.single p (twoEquiv (AdjoinRoot p.val) y) := by
  simp only [residueTwoMap, DFinsupp.mapRange.linearMap_apply,
    DFinsupp.mapRange_single, LinearEquiv.coe_coe]

/-- The entire actual finite residue vector commutes with the old presentations. -/
theorem residueTwoMap_totalResidue (x : K (RatFunc k) 3) :
    residueTwoMap (totalResidue 2 x) =
      MilnorK.K3.PolynomialResidue.totalResidue (threeEquiv (RatFunc k) x) := by
  apply DFinsupp.ext
  intro p
  exact twoEquiv_residueAt p.val x

/-- Surjectivity of actual finite residues compares the total norms on all vectors. -/
theorem twoEquiv_totalNorm
    (y : Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) 2) :
    twoEquiv k (totalNorm 2 y) = MilnorK.K3.PolynomialNorm.totalNorm (residueTwoMap y) := by
  obtain ⟨x, rfl⟩ := totalResidue_surjective 2 y
  rw [totalNorm_totalResidue, map_neg, twoEquiv_infinityResidue,
    residueTwoMap_totalResidue, MilnorK.K3.PolynomialNorm.totalNorm_totalResidue]

/-- The actual degree-two polynomial norm equals the original norm on every class. -/
theorem twoEquiv_polynomialNorm (p : MonicIrreducible k)
    (x : K (AdjoinRoot p.val) 2) :
    twoEquiv k (polynomialNorm 2 p x) =
      MilnorK.K3.PolynomialNorm.polynomialNorm p (twoEquiv (AdjoinRoot p.val) x) := by
  classical
  simpa only [totalNorm_single, residueTwoMap_single,
    MilnorK.K3.PolynomialNorm.totalNorm_single] using twoEquiv_totalNorm (DFinsupp.single p x)

/-- Equality of the actual polynomial norm squares as linear maps. -/
theorem twoEquiv_polynomialNorm_square (p : MonicIrreducible k) :
    (twoEquiv k).toLinearMap.comp (polynomialNorm 2 p) =
      (MilnorK.K3.PolynomialNorm.polynomialNorm p).comp
        (twoEquiv (AdjoinRoot p.val)).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact twoEquiv_polynomialNorm p x

end PolynomialNorm
end MilnorK
