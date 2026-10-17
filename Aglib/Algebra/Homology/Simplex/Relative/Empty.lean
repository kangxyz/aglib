/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Singleton
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Original degree-zero cohomology for empty required support

Cycles in degree zero are exactly constant vertex cochains. Evaluation at
any chosen vertex therefore identifies the original native degree-zero
homology with the scalar module. The comparison is independent of that
vertex and retains the original cycles quotient and constant augmentation.
Positive exactness is already given by insertion of a vertex in `Singleton`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v} {R : Type u} [Ring R]

/-- The original zero-simplex at the chosen vertex, with no required support. -/
def vertexTuple (j : ι) : Tuple (∅ : Set ι) 0 := ⟨fun _ => j, Set.empty_subset _⟩

/-- The original one-simplex joining the indicated vertices. -/
def vertexPair (i j : ι) : Tuple (∅ : Set ι) 1 :=
  ⟨Fin.cons i (fun _ => j), Set.empty_subset _⟩

/-- The native degree-zero cocycle equation equates the values on any two vertices. -/
theorem emptySupport_cycle_eval_eq (c : (complex R (∅ : Set ι)).cycles 0) (i j : ι) :
    (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple i) =
      (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple j) := by
  have hx := ConcreteCategory.congr_hom ((complex R (∅ : Set ι)).iCycles_d 0 1) c
  change (complex R (∅ : Set ι)).d 0 1 ((complex R (∅ : Set ι)).iCycles 0 c) = 0 at hx
  have h := congrFun hx (vertexPair i j)
  change (complex R (∅ : Set ι)).d 0 1 ((complex R (∅ : Set ι)).iCycles 0 c)
    (vertexPair i j) = 0 at h
  rw [d_apply, Fin.sum_univ_two] at h
  have hzero : (vertexPair i j).val ∘ (0 : Fin 2).succAbove = (vertexTuple j).val := by
    funext k
    simp [vertexPair, vertexTuple]
  have hone : (vertexPair i j).val ∘ (1 : Fin 2).succAbove = (vertexTuple i).val := by
    funext k
    rw [Fin.eq_zero k]
    rfl
  rw [hzero, hone, extendByZero_apply, extendByZero_apply] at h
  have he : (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple j) -
      (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple i) = 0 := by
    simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul,
      sub_eq_add_neg] using h
  exact (sub_eq_zero.mp he).symm

/-- Every original zero-cycle is constant on all its original tuples. -/
theorem emptySupport_cycle_constant (j : ι) (c : (complex R (∅ : Set ι)).cycles 0)
    (a : Tuple (∅ : Set ι) 0) :
    (complex R (∅ : Set ι)).iCycles 0 c a =
      (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple j) := by
  have ha : a = vertexTuple (a.val 0) := by
    apply Subtype.ext
    funext k
    rw [Fin.eq_zero k]
    rfl
  rw [ha]
  exact emptySupport_cycle_eval_eq c _ j

/-- The original constant cochain, as an actual native zero-cycle. -/
def emptySupportConstantCycle (r : R) : (complex R (∅ : Set ι)).cycles 0 :=
  (complex R (∅ : Set ι)).cyclesMk (fun _ => r) 1 (by simp) (by
    change (complex R (∅ : Set ι)).d 0 1 (fun _ => r) = 0
    funext a
    change (complex R (∅ : Set ι)).d 0 1 (fun _ => r) a = 0
    rw [d_apply, Fin.sum_univ_two]
    simp [extendByZero])

theorem i_emptySupportConstantCycle (r : R) :
    (complex R (∅ : Set ι)).iCycles 0 (emptySupportConstantCycle r) = fun _ => r :=
  (complex R (∅ : Set ι)).i_cyclesMk _ _ _ _

/-- Canonical coercion form of `i_emptySupportConstantCycle`
for simplification. -/
@[simp]
private theorem i_emptySupportConstantCycle' (r : R) :
    (show (complex R (∅ : Set ι)).cycles 0 →ₗ[R] Cochains R (∅ : Set ι) 0 from
      ((complex R (∅ : Set ι)).iCycles 0).hom) (emptySupportConstantCycle r) = fun _ => r := by
  exact i_emptySupportConstantCycle (R := R) (ι := ι) r

/-- Actual scalar-linear evaluation of an original zero-cycle at a vertex. -/
def emptySupportCyclesEval (j : ι) : (complex R (∅ : Set ι)).cycles 0 →ₗ[R] R :=
  (LinearMap.proj (vertexTuple j)).comp ((complex R (∅ : Set ι)).iCycles 0).hom

/-- Actual zero-cycles are the scalar module, through the original evaluation. -/
def emptySupportCyclesLinearEquiv (j : ι) : (complex R (∅ : Set ι)).cycles 0 ≃ₗ[R] R :=
  LinearEquiv.ofBijective (emptySupportCyclesEval j) (by
    constructor
    · intro x y h
      apply (ModuleCat.mono_iff_injective ((complex R (∅ : Set ι)).iCycles 0)).mp inferInstance
      funext a
      calc
        (complex R (∅ : Set ι)).iCycles 0 x a =
            (complex R (∅ : Set ι)).iCycles 0 x (vertexTuple j) := emptySupport_cycle_constant j x a
        _ = (complex R (∅ : Set ι)).iCycles 0 y (vertexTuple j) := h
        _ = (complex R (∅ : Set ι)).iCycles 0 y a := (emptySupport_cycle_constant j y a).symm
    · intro r
      refine ⟨emptySupportConstantCycle r, ?_⟩
      change (complex R (∅ : Set ι)).iCycles 0 (emptySupportConstantCycle r) (vertexTuple j) = r
      rw [i_emptySupportConstantCycle])

/-- The original native H0 with empty required support is the scalar module,
through its original cycles quotient and vertex evaluation. -/
def emptySupportHomologyZeroLinearEquiv (j : ι) :
    (complex R (∅ : Set ι)).homology 0 ≃ₗ[R] R :=
  (complex R (∅ : Set ι)).isoHomologyπ₀.symm.toLinearEquiv.trans
    (emptySupportCyclesLinearEquiv j)

/-- The degree-zero comparison retains the actual cycles quotient and evaluation. -/
theorem emptySupportHomologyZeroLinearEquiv_homologyπ (j : ι)
    (c : (complex R (∅ : Set ι)).cycles 0) :
    emptySupportHomologyZeroLinearEquiv j ((complex R (∅ : Set ι)).homologyπ 0 c) =
      (complex R (∅ : Set ι)).iCycles 0 c (vertexTuple j) := by
  change (complex R (∅ : Set ι)).iCycles 0
    ((complex R (∅ : Set ι)).isoHomologyπ₀.inv ((complex R (∅ : Set ι)).homologyπ 0 c))
    (vertexTuple j) = _
  have hπ : (complex R (∅ : Set ι)).isoHomologyπ₀.inv
      ((complex R (∅ : Set ι)).homologyπ 0 c) = c :=
    Iso.hom_inv_id_apply (complex R (∅ : Set ι)).isoHomologyπ₀ c
  rw [hπ]

/-- The original constant augmentation is the inverse scalar normalization. -/
@[simp]
theorem emptySupportHomologyZeroLinearEquiv_constant (j : ι) (r : R) :
    emptySupportHomologyZeroLinearEquiv j
      ((complex R (∅ : Set ι)).homologyπ 0 (emptySupportConstantCycle r)) = r := by
  rw [emptySupportHomologyZeroLinearEquiv_homologyπ, i_emptySupportConstantCycle]

/-- The displayed H0 comparison is independent of the chosen vertex. -/
theorem emptySupportHomologyZeroLinearEquiv_eq (i j : ι) :
    emptySupportHomologyZeroLinearEquiv (R := R) i = emptySupportHomologyZeroLinearEquiv j := by
  apply LinearEquiv.ext
  intro x
  let c := (complex R (∅ : Set ι)).isoHomologyπ₀.inv x
  have hc : (complex R (∅ : Set ι)).homologyπ 0 c = x :=
    Iso.inv_hom_id_apply (complex R (∅ : Set ι)).isoHomologyπ₀ x
  rw [← hc, emptySupportHomologyZeroLinearEquiv_homologyπ,
    emptySupportHomologyZeroLinearEquiv_homologyπ]
  exact emptySupport_cycle_eval_eq c i j

end AlgebraicTopology.RelativeSimplex
