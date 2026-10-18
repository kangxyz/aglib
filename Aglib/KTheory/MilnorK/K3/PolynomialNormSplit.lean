/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormBaseChange
public import Aglib.RingTheory.AdjoinRootScalarBranches

/-!
# Split polynomial norms on the original Milnor K₂ groups

For a monic linear polynomial, root evaluation is a literal equivalence with
its coefficient field. The proved polynomial degree formula identifies its
actual K₂ norm with the K₂ map of that equivalence. The full coefficient
base-change formula therefore becomes a sum over every original finite branch
when the original polynomial splits in the target field.

Characteristic zero is used only for the inherited coefficient base-change
formula. There is no norm-presentation independence, arbitrary-extension tower,
or higher-K norm hypothesis. This is a prerequisite for principal-unit descent,
not a principal-unit or norm/tame theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k L : Type*} [Field k] [Field L]

/-- The root of a monic linear polynomial is the negative constant coefficient. -/
theorem linear_eval_zero (q : MonicIrreducible L) (hq : q.val.natDegree = 1) :
    q.val.eval₂ (RingHom.id L) (-q.val.coeff 0) = 0 := by
  conv_lhs => rw [q.property.1.eq_X_add_C hq]
  simp

/-- Literal evaluation of the original quotient at its unique linear root. -/
def rootEvaluation (q : MonicIrreducible L) (hq : q.val.natDegree = 1) :
    AdjoinRoot q.val →+* L :=
  AdjoinRoot.lift (RingHom.id L) (-q.val.coeff 0) (linear_eval_zero q hq)

@[simp]
theorem rootEvaluation_mk (q : MonicIrreducible L) (hq : q.val.natDegree = 1)
    (a : L[X]) :
    rootEvaluation q hq (AdjoinRoot.mk q.val a) = a.eval (-q.val.coeff 0) := by
  simp [rootEvaluation]

@[simp]
theorem rootEvaluation_root (q : MonicIrreducible L) (hq : q.val.natDegree = 1) :
    rootEvaluation q hq (AdjoinRoot.root q.val) = -q.val.coeff 0 :=
  AdjoinRoot.lift_root _

theorem rootEvaluation_algebraMap (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) (a : L) :
    rootEvaluation q hq (algebraMap L (AdjoinRoot q.val) a) = a := by
  change AdjoinRoot.lift (RingHom.id L) _ _ (AdjoinRoot.of q.val a) = a
  exact AdjoinRoot.lift_of _

/-- Root evaluation, with inverse equal to the original coefficient inclusion. -/
def rootEvaluationEquiv (q : MonicIrreducible L) (hq : q.val.natDegree = 1) :
    AdjoinRoot q.val ≃ₐ[L] L :=
  { RingEquiv.ofBijective (rootEvaluation q hq)
      ⟨(rootEvaluation q hq).injective,
        fun a => ⟨algebraMap L (AdjoinRoot q.val) a, rootEvaluation_algebraMap q hq a⟩⟩ with
    commutes' := rootEvaluation_algebraMap q hq }

theorem rootEvaluationEquiv_toRingHom (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) :
    (rootEvaluationEquiv q hq).toRingHom = rootEvaluation q hq := rfl

theorem rootEvaluationEquiv_symm_toRingHom (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) :
    (rootEvaluationEquiv q hq).symm.toRingHom = algebraMap L (AdjoinRoot q.val) := by
  ext a
  apply (rootEvaluationEquiv q hq).injective
  exact (rootEvaluationEquiv q hq).apply_symm_apply a |>.trans
    (rootEvaluation_algebraMap q hq a).symm

/-- A degree-one polynomial norm is the actual K₂ map of root evaluation. -/
theorem polynomialNorm_eq_map_rootEvaluation (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) :
    polynomialNorm q = MilnorK.K2.map (rootEvaluation q hq) := by
  have hcomp : (algebraMap L (AdjoinRoot q.val)).comp (rootEvaluation q hq) =
      RingHom.id (AdjoinRoot q.val) := by
    rw [← rootEvaluationEquiv_toRingHom, ← rootEvaluationEquiv_symm_toRingHom q hq]
    apply RingHom.ext
    intro x
    exact (rootEvaluationEquiv q hq).symm_apply_apply x
  apply LinearMap.ext
  intro z
  have hz : MilnorK.K2.map (algebraMap L (AdjoinRoot q.val))
      (MilnorK.K2.map (rootEvaluation q hq) z) = z := by
    rw [← LinearMap.comp_apply, ← MilnorK.K2.map_comp, hcomp, MilnorK.K2.map_id,
      LinearMap.id_apply]
  calc
    polynomialNorm q z = polynomialNorm q
        (MilnorK.K2.map (algebraMap L (AdjoinRoot q.val))
          (MilnorK.K2.map (rootEvaluation q hq) z)) := congrArg (polynomialNorm q) hz.symm
    _ = MilnorK.K2.map (rootEvaluation q hq) z := by
      rw [polynomialNorm_map_constants, hq, Nat.cast_one, one_smul]

/-- The degree-one formula explicitly uses the root-evaluation equivalence. -/
theorem polynomialNorm_eq_map_rootEvaluationEquiv (q : MonicIrreducible L)
    (hq : q.val.natDegree = 1) :
    polynomialNorm q = MilnorK.K2.map (rootEvaluationEquiv q hq).toRingHom :=
  polynomialNorm_eq_map_rootEvaluation q hq

/-- Splitting makes every member of the original full factor set linear. -/
theorem natDegree_eq_one_of_mem_placesAbove (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : MonicIrreducible L) (hq : q ∈ placesAbove φ p) :
    q.val.natDegree = 1 :=
  (hp.of_dvd (Polynomial.map_ne_zero p.property.2.ne_zero)
    ((mem_placesAbove φ p q).mp hq)).natDegree_eq_one_of_irreducible q.property.2

/-- The original source field embedded in a split branch, by literal quotient
mapping followed by evaluation at that branch's linear root. -/
def splitBranchMap (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) :
    AdjoinRoot p.val →+* L :=
  (rootEvaluation q.val (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property)).comp
    (adjoinRootMap φ p.val q.val.val ((mem_placesAbove φ p q.val).mp q.property))

/-- The embedding uses the whole scalar extension and its literal branch
quotient before evaluating the branch root. -/
theorem splitBranchMap_eq_eval_divisor_scalarMap (φ : k →+* L)
    (p : MonicIrreducible k) (hp : (p.val.map φ).Splits)
    (q : {q // q ∈ placesAbove φ p}) :
    splitBranchMap φ p hp q =
      (rootEvaluation q.val
        (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property)).comp
          ((AdjoinRoot.divisorMap (p.val.map φ) q.val.val
            ((mem_placesAbove φ p q.val).mp q.property)).comp
              (AdjoinRoot.scalarMap φ p.val)) := by
  rw [AdjoinRoot.divisorMap_comp_scalarMap]
  rfl

@[simp]
theorem splitBranchMap_mk (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) (a : k[X]) :
    splitBranchMap φ p hp q (AdjoinRoot.mk p.val a) =
      a.eval₂ φ (-q.val.val.coeff 0) := by
  simp only [splitBranchMap, RingHom.comp_apply, adjoinRootMap_mk,
    rootEvaluation_mk, Polynomial.eval_map]

theorem splitBranchMap_algebraMap (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) (a : k) :
    splitBranchMap φ p hp q (algebraMap k (AdjoinRoot p.val) a) = φ a := by
  simp only [splitBranchMap, RingHom.comp_apply, adjoinRootMap_algebraMap,
    rootEvaluation_algebraMap]

@[simp]
theorem splitBranchMap_root (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) :
    splitBranchMap φ p hp q (AdjoinRoot.root p.val) = -q.val.val.coeff 0 := by
  simp [splitBranchMap]

/-- Each branch map is an actual field embedding. -/
theorem splitBranchMap_injective (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) (q : {q // q ∈ placesAbove φ p}) :
    Function.Injective (splitBranchMap φ p hp q) :=
  (splitBranchMap φ p hp q).injective

/-- Distinct members of the original factor set yield distinct embeddings. -/
theorem splitBranchMap_injective_index (φ : k →+* L) (p : MonicIrreducible k)
    (hp : (p.val.map φ).Splits) : Function.Injective (splitBranchMap φ p hp) := by
  intro q r h
  have hr := RingHom.congr_fun h (AdjoinRoot.root p.val)
  simp only [splitBranchMap_root, neg_inj] at hr
  apply Subtype.ext
  apply Subtype.ext
  rw [q.val.property.1.eq_X_add_C (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property),
    r.val.property.1.eq_X_add_C (natDegree_eq_one_of_mem_placesAbove φ p hp r.val r.property), hr]

open scoped Classical in
/-- After a splitting coefficient extension, restriction of the actual norm
is the sum of the actual maps of all original linear branches. -/
theorem polynomialNorm_restrict_of_splits [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits)
    (z : MilnorK.K2.Group (AdjoinRoot p.val)) :
    MilnorK.K2.map φ (polynomialNorm p z) =
      ∑ q ∈ (placesAbove φ p).attach, MilnorK.K2.map (splitBranchMap φ p hp q) z := by
  rw [polynomialNorm_restrict]
  apply Finset.sum_congr rfl
  intro q _
  rw [polynomialNorm_eq_map_rootEvaluation q.val
    (natDegree_eq_one_of_mem_placesAbove φ p hp q.val q.property)]
  exact (LinearMap.congr_fun (MilnorK.K2.map_comp _ _) z).symm

open scoped Classical in
/-- The split formula is an equality of maps on the original integer modules. -/
theorem polynomialNorm_comp_restrict_of_splits [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits) :
    (MilnorK.K2.map φ).comp (polynomialNorm p) =
      ∑ q ∈ (placesAbove φ p).attach, MilnorK.K2.map (splitBranchMap φ p hp q) := by
  apply LinearMap.ext
  intro z
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    polynomialNorm_restrict_of_splits φ p hp z

open scoped Classical in
/-- Both arbitrary source-symbol coordinates are evaluated in each branch. -/
theorem polynomialNorm_restrict_symbol_of_splits [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) (hp : (p.val.map φ).Splits)
    (a b : (AdjoinRoot p.val)ˣ) :
    MilnorK.K2.map φ (polynomialNorm p (MilnorK.K2.symbol a b)) =
      ∑ q ∈ (placesAbove φ p).attach,
        MilnorK.K2.symbol (Units.map (splitBranchMap φ p hp q).toMonoidHom a)
          (Units.map (splitBranchMap φ p hp q).toMonoidHom b) := by
  simpa only [MilnorK.K2.map_symbol] using
    polynomialNorm_restrict_of_splits φ p hp (MilnorK.K2.symbol a b)

end MilnorK.K3.PolynomialNorm
