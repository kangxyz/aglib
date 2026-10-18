/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalResiduePrime
public import Aglib.RingTheory.AdjoinRootCoefficientTowerBranches

/-!
# Composition of actual rational finite-place residue norm sums

All residue field actions are the original quotient maps. The full factor
bijection retains the upper polynomial literally. General finite norm tower
compatibility then combines each successive residue norm, without assuming a
general norm-residue square.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  residueRootFinite residueRootCharZero primeRationalFinite

universe u

/-- The full actual finite-place residue norm sum for the original coefficient extension. -/
def rationalResidueNormSum
    (k E : Type u) [Field k] [CharZero k] [Field E] [Algebra k E]
    [FiniteDimensional k E] (h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc E) (n + 1)) : K (AdjoinRoot h.val) n := by
  classical
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k E))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k E))) := Fintype.ofFinite _
  exact ∑ r : IrreducibleBranch (h.val.map (algebraMap k E)),
    let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
      finiteDimensional_scalarBranch_residue h r
    finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
      (residueAt r.val.val n x)

/-- The two original residue-field norm maps compose to the direct one at each
actual successive branch, with the upper quotient field literally unchanged. -/
theorem finiteExtensionNorm_coefficient_residue_tower
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (h : MonicIrreducible k)
    (r : IrreducibleBranch (h.val.map (algebraMap k L)))
    (q : IrreducibleBranch (r.val.val.map (algebraMap L E)))
    (n : ℕ) (z : K (AdjoinRoot q.val.val) n) :
    let v := coefficientTowerBranchOfAlgebra (k := k) (L := L) (E := E) h.val ⟨r, q⟩
    let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
      finiteDimensional_scalarBranch_residue h r
    let : FiniteDimensional (AdjoinRoot r.val.val) (AdjoinRoot q.val.val) :=
      finiteDimensional_scalarBranch_residue r.val q
    let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot v.val.val) :=
      finiteDimensional_scalarBranch_residue h v
    finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot v.val.val) n z =
      finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
        (finiteExtensionNorm (AdjoinRoot r.val.val) (AdjoinRoot q.val.val) n z) := by
  let v := coefficientTowerBranchOfAlgebra (k := k) (L := L) (E := E) h.val ⟨r, q⟩
  let : Algebra (AdjoinRoot h.val) (AdjoinRoot q.val.val) := scalarBranchAlgebra h.val v
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
    finiteDimensional_scalarBranch_residue h r
  let : FiniteDimensional (AdjoinRoot r.val.val) (AdjoinRoot q.val.val) :=
    finiteDimensional_scalarBranch_residue r.val q
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot q.val.val) :=
    finiteDimensional_scalarBranch_residue h v
  let : IsScalarTower (AdjoinRoot h.val) (AdjoinRoot r.val.val) (AdjoinRoot q.val.val) :=
    adjoinRootMap_isScalarTowerOfAlgebra h.val r.val.val q.val.val
      r.property q.property v.property
  exact finiteExtensionNorm_tower (AdjoinRoot r.val.val) (AdjoinRoot q.val.val) n z

/-- Under the explicitly stated upper finite-place induction hypothesis, the
actual lower residue sum of the upper rational norm is the direct residue sum. -/
theorem rationalResidueNormSum_norm_of_upper_squares
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (n : ℕ)
    (upper : ∀ r : MonicIrreducible L, ∀ y : K (RatFunc E) (n + 1),
      residueAt r.val n (finiteExtensionNorm (RatFunc L) (RatFunc E) (n + 1) y) =
        rationalResidueNormSum L E r n y)
    (h : MonicIrreducible k) (x : K (RatFunc E) (n + 1)) :
    rationalResidueNormSum k L h n
      (finiteExtensionNorm (RatFunc L) (RatFunc E) (n + 1) x) =
        rationalResidueNormSum k E h n x := by
  classical
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k L))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k L))) := Fintype.ofFinite _
  let : ∀ r : IrreducibleBranch (h.val.map (algebraMap k L)),
      Finite (IrreducibleBranch (r.val.val.map (algebraMap L E))) :=
    fun r => finite_irreducibleBranch _ (r.val.property.1.map _)
  let : ∀ r : IrreducibleBranch (h.val.map (algebraMap k L)),
      Fintype (IrreducibleBranch (r.val.val.map (algebraMap L E))) :=
    fun _ => Fintype.ofFinite _
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k E))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k E))) := Fintype.ofFinite _
  unfold rationalResidueNormSum
  symm
  refine (sum_coefficientTowerBranchEquivOfAlgebra (L := L) h.val h.property.1.ne_zero _).trans ?_
  apply Finset.sum_congr rfl
  intro r _
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
    finiteDimensional_scalarBranch_residue h r
  refine Eq.trans ?_
    (congrArg (finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n)
      (upper r.val x)).symm
  unfold rationalResidueNormSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact finiteExtensionNorm_coefficient_residue_tower h r q n (residueAt q.val.val n x)

/-- Actual finite-place compatibility is closed under coefficient-field towers.
Both residue-square hypotheses are explicit induction premises, not global laws. -/
theorem residueAt_finiteExtensionNorm_rational_of_tower
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (n : ℕ)
    (lower : ∀ h : MonicIrreducible k, ∀ y : K (RatFunc L) (n + 1),
      residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) y) =
        rationalResidueNormSum k L h n y)
    (upper : ∀ r : MonicIrreducible L, ∀ y : K (RatFunc E) (n + 1),
      residueAt r.val n (finiteExtensionNorm (RatFunc L) (RatFunc E) (n + 1) y) =
        rationalResidueNormSum L E r n y)
    (h : MonicIrreducible k) (x : K (RatFunc E) (n + 1)) :
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      rationalResidueNormSum k E h n x := by
  rw [finiteExtensionNorm_rational_tower L E (n + 1), LinearMap.comp_apply, lower]
  exact rationalResidueNormSum_norm_of_upper_squares n upper h x

end MilnorK
