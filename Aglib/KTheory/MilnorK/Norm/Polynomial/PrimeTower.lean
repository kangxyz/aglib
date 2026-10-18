/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeDiamond
public import Aglib.KTheory.MilnorK.Norm.Polynomial.Split
public import Aglib.RingTheory.AdjoinRootTowerBranch

/-!
# The normal-prime base step of actual polynomial norm towers

The normal-prime diamond specializes along a linear matched branch. Its
upper presentation is identified with the original top field by the actual
quotient equivalence, not by an assumed norm-compatibility law.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open MilnorK.K3.PolynomialNorm (rootEvaluation rootEvaluationEquiv
  rootEvaluationEquiv_symm_toRingHom)

variable {k : Type*} [Field k]

/-- A degree-one norm is induced by its actual base-field algebra equivalence. -/
theorem polynomialNorm_eq_map_algEquiv_self (q : MonicIrreducible k)
    (hq : q.val.natDegree = 1) (ε : AdjoinRoot q.val ≃ₐ[k] k) (n : ℕ) :
    polynomialNorm n q = map n ε.toRingHom := by
  rw [polynomialNorm_eq_map_rootEvaluation n q hq]
  congr 1
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := (rootEvaluationEquiv q hq).symm.surjective x
  change rootEvaluation q hq ((rootEvaluationEquiv q hq).symm.toRingHom a) =
    ε ((rootEvaluationEquiv q hq).symm.toRingHom a)
  rw [rootEvaluationEquiv_symm_toRingHom,
    MilnorK.K3.PolynomialNorm.rootEvaluation_algebraMap, AlgEquiv.commutes]
  rfl

/-- The diamond gives an actual tower whenever its matched branch is linear.
The top-field identification is the composite of the two literal equivalences. -/
theorem polynomialNorm_prime_tower_of_linear_branch [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (hr : (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val.val.natDegree = 1)
    (ε : AdjoinRoot (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val.val
      ≃ₐ[AdjoinRoot h.val] AdjoinRoot h.val) (n : ℕ) (z : K (AdjoinRoot q.val.val) n) :
    polynomialNorm n p (polynomialNorm n q.val z) =
      polynomialNorm n h (map n
        ((AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).trans
          ε.toRingEquiv).toRingHom z) := by
  rw [polynomialNorm_prime_diamond p hp h q n z,
    polynomialNorm_eq_map_algEquiv_self _ hr ε]
  apply congrArg (polynomialNorm n h)
  exact (LinearMap.congr_fun (map_comp n
    (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).toRingHom ε.toRingHom) z).symm

/-- The actual normal-prime base tower, with its constructed top-field equivalence. -/
theorem polynomialNorm_prime_tower [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h.val) (n : ℕ)
    (z : K (AdjoinRoot (AdjoinRoot.towerBranch p.val h.val f).val.val) n) :
    polynomialNorm n p (polynomialNorm n (AdjoinRoot.towerBranch p.val h.val f).val z) =
      polynomialNorm n h (map n (AdjoinRoot.towerBranchRingEquiv p.val h.val f).toRingHom z) :=
  polynomialNorm_prime_tower_of_linear_branch p hp h (AdjoinRoot.towerBranch p.val h.val f)
    (AdjoinRoot.towerBranch_matched_natDegree p.val h.val f)
    (AdjoinRoot.towerBranchTargetEquiv p.val h.val f) n z

/-- On the original top field, its original norm factors through the actual
normal-prime subfield using the literal upper quotient map. -/
theorem polynomialNorm_eq_prime_tower [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h.val) (n : ℕ)
    (x : K (AdjoinRoot h.val) n) :
    polynomialNorm n h x =
      polynomialNorm n p (polynomialNorm n (AdjoinRoot.towerBranch p.val h.val f).val
        (map n (adjoinRootMap (algebraMap k (AdjoinRoot p.val)) h.val
          (AdjoinRoot.towerBranch p.val h.val f).val.val
          (AdjoinRoot.towerBranch p.val h.val f).property) x)) := by
  rw [polynomialNorm_prime_tower p hp]
  apply congrArg (polynomialNorm n h)
  rw [← AdjoinRoot.towerBranchRingEquiv_symm_toRingHom]
  rw [← LinearMap.comp_apply, ← map_comp]
  have he : (AdjoinRoot.towerBranchRingEquiv p.val h.val f).toRingHom.comp
      (AdjoinRoot.towerBranchRingEquiv p.val h.val f).symm.toRingHom =
      RingHom.id (AdjoinRoot h.val) := by
    apply RingHom.ext
    intro a
    exact (AdjoinRoot.towerBranchRingEquiv p.val h.val f).apply_symm_apply a
  rw [he, map_id]
  rfl

end MilnorK.PolynomialNorm
