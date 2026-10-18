/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.BaseChange
public import Aglib.KTheory.MilnorK.K3.PolynomialNormSplit

/-!
# Split polynomial norms in every Milnor degree

The existing literal linear-root evaluations and split-branch field maps
work independently of Milnor degree. The actual degree law identifies a
linear polynomial norm with the map of that root evaluation. Coefficient
base change therefore becomes the sum of the branch field maps in all
degrees. No arbitrary finite-extension norm is introduced.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open MilnorK.K3.PolynomialNorm (rootEvaluation rootEvaluationEquiv
  rootEvaluationEquiv_toRingHom rootEvaluationEquiv_symm_toRingHom
  splitBranchMap natDegree_eq_one_of_mem_placesAbove)

variable {k L : Type*} [Field k] [Field L]

/-- A linear polynomial norm is the actual Milnor map of root evaluation,
in every degree and in arbitrary characteristic. -/
theorem polynomialNorm_eq_map_rootEvaluation (n : ℕ) (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) :
    polynomialNorm n q = MilnorK.map n (rootEvaluation q hq) := by
  have hcomp : (algebraMap L (AdjoinRoot q.val)).comp (rootEvaluation q hq) =
      RingHom.id (AdjoinRoot q.val) := by
    rw [← rootEvaluationEquiv_toRingHom, ← rootEvaluationEquiv_symm_toRingHom q hq]
    apply RingHom.ext
    intro x
    exact (rootEvaluationEquiv q hq).symm_apply_apply x
  apply LinearMap.ext
  intro z
  have hz : MilnorK.map n (algebraMap L (AdjoinRoot q.val))
      (MilnorK.map n (rootEvaluation q hq) z) = z := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hcomp, MilnorK.map_id,
      LinearMap.id_apply]
  calc
    polynomialNorm n q z = polynomialNorm n q
        (MilnorK.map n (algebraMap L (AdjoinRoot q.val))
          (MilnorK.map n (rootEvaluation q hq) z)) := congrArg (polynomialNorm n q) hz.symm
    _ = MilnorK.map n (rootEvaluation q hq) z := by
      rw [polynomialNorm_map_constants, hq, Nat.cast_one, one_smul]

open scoped Classical in
/-- After a splitting coefficient extension, each polynomial-presentation norm
restricts to the sum of all actual branch field maps. -/
theorem polynomialNorm_restrict_of_splits [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits)
    (z : K (AdjoinRoot p.val) n) :
    MilnorK.map n φ (polynomialNorm n p z) =
      ∑ q ∈ (placesAbove φ p).attach, MilnorK.map n (splitBranchMap φ p hp q) z := by
  rw [polynomialNorm_restrict]
  apply Finset.sum_congr rfl
  intro q _
  rw [polynomialNorm_eq_map_rootEvaluation n q.val
    (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property)]
  exact (LinearMap.congr_fun (MilnorK.map_comp n _ _) z).symm

end MilnorK.PolynomialNorm
