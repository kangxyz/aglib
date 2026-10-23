/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Tsen.RationalFunctionSystem
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Tsen's theorem for finite extensions of a rational function field

Expand a homogeneous form in a finite `K(T)`-basis. Its coordinate equations
are homogeneous forms of the same degree, with the number of variables and
equations both multiplied by the basis size. The rational-function-system
supplier gives a nonzero solution, and basis independence preserves nonzeroness.
No separability or perfection assumption on the finite extension is required.
-/

@[expose] public section

namespace Field

/-- Every finite extension of `K(T)`, for algebraically closed `K`, is C₁. -/
theorem isC1_finite_ratFunc (K E : Type*) [Field K] [IsAlgClosed K] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E] : IsC1 E := by
  classical
  intro n d p hd hdn hp
  let r := Module.finrank (RatFunc K) E
  let b := Module.finBasis (RatFunc K) E
  let v : Fin n → MvPolynomial (Fin n × Fin r) E :=
    fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (i, j)
  let Q := MvPolynomial.eval₂ MvPolynomial.C v p
  have hQ : Q.IsHomogeneous d := by
    apply (show (1 * d) = d by simp) ▸ hp.eval₂ MvPolynomial.C v
      (fun _ => MvPolynomial.isHomogeneous_C _ _) ?_
    intro i
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact (MvPolynomial.isHomogeneous_X _ _).C_mul _
  let P : Fin r → MvPolynomial (Fin n × Fin r) (RatFunc K) :=
    fun j => AddMonoidAlgebra.map (b.coord j).toAddMonoidHom Q
  have hP : ∀ j, (P j).IsHomogeneous d := fun j => hQ.map_addHom _
  have hr : 0 < r := Module.finrank_pos
  have hcount : Fintype.card (Fin r) * d < Fintype.card (Fin n × Fin r) := by
    simp only [Fintype.card_fin, Fintype.card_prod]
    simpa only [Nat.mul_comm r] using Nat.mul_lt_mul_of_pos_right hdn hr
  obtain ⟨a, ha, hPa⟩ := MvPolynomial.exists_ratFunc_solution P hd hP hcount
  let x : Fin n → E := fun i => ∑ j, a (i, j) • b j
  have heval : MvPolynomial.eval (fun j => algebraMap (RatFunc K) E (a j)) Q =
      MvPolynomial.eval x p := by
    dsimp only [Q]
    rw [MvPolynomial.eval_eval₂]
    have hc : (MvPolynomial.eval (fun j => algebraMap (RatFunc K) E (a j))).comp
        MvPolynomial.C = RingHom.id E := by
      apply RingHom.ext
      intro z
      simp only [RingHom.comp_apply, MvPolynomial.eval_C, RingHom.id_apply]
    rw [hc, MvPolynomial.eval₂_id]
    apply congrArg (fun y => MvPolynomial.eval y p)
    funext i
    simp only [v, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def, mul_comm]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply ha
    funext j
    have hrepr := congrArg (fun z => (b.repr z : Fin r → RatFunc K))
      (congrFun hx j.1)
    simp only [x, Pi.zero_apply, map_zero, Finsupp.coe_zero] at hrepr
    exact (congrFun (b.repr_sum_self (fun t => a (j.1, t))) j.2).symm.trans
      (congrFun hrepr j.2)
  · apply b.forall_coord_eq_zero_iff.mp
    intro j
    have hcoord := MvPolynomial.eval_map_linearMap (b.coord j) Q a
    have hcoord' : MvPolynomial.eval a (P j) =
        b.coord j (MvPolynomial.eval (fun j => algebraMap (RatFunc K) E (a j)) Q) := by
      simpa only [P, Algebra.algebraMap_self, RingHom.id_apply] using hcoord
    rw [heval] at hcoord'
    exact hcoord'.symm.trans (hPa j)

end Field
