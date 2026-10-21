/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.DegreeZeroGeneration
public import Aglib.RingTheory.AssociatedGraded.Multiplication

/-! # Original coordinate scalars on external associated-graded modules -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DirectSum GradedMonoid
universe u v w
namespace Ideal
variable {A : Type u} [CommRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B]
  (M : ℕ → Type w) [∀ n, AddCommGroup (M n)]
  [∀ n, Module B (M n)] [∀ n, Module A (M n)]
  [∀ n, IsScalarTower A B (M n)]
  [DirectSum.Gmodule (fun n => I.associatedGradedGrading n) M]

/-- The native direct sum carries the action induced by its original homogeneous maps. -/
local instance : Module I.associatedGraded (⨁ n, M n) := I.associatedGradedExternalModule M

omit [Algebra A B] [∀ n, Module A (M n)] [∀ n, IsScalarTower A B (M n)] in
/-- Original coordinate-linear homogeneous maps commute with coordinate scalars
on the full native external associated-graded module. -/
theorem associatedGradedExternalModule_smulComm
    (hlinear : ∀ r n (a : I.associatedGradedGrading r) (b : B) (x : M n),
      GSMul.smul (A := fun k => I.associatedGradedGrading k) (M := M) a (b • x) =
        b • GSMul.smul (A := fun k => I.associatedGradedGrading k) (M := M) a x) :
    SMulCommClass B I.associatedGraded (⨁ n, M n) where
  smul_comm b s x := by
    change b • (DirectSum.Gmodule.smulAddMonoidHom
      (fun n => I.associatedGradedGrading n) M
      (DirectSum.decompose I.associatedGradedGrading s) x) =
      DirectSum.Gmodule.smulAddMonoidHom
        (fun n => I.associatedGradedGrading n) M
        (DirectSum.decompose I.associatedGradedGrading s) (b • x)
    generalize DirectSum.decompose I.associatedGradedGrading s = t
    induction t using DirectSum.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply, smul_zero]
    | of r a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | of n x =>
        simp only [← DirectSum.of_smul,
          DirectSum.Gmodule.smulAddMonoidHom_apply_of_of, hlinear]
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | add s t hs ht =>
      simp only [map_add, AddMonoidHom.add_apply, smul_add, hs, ht]

/-- Equality of the actual degree-zero action with the original base scalar
makes the external module a compatible scalar tower. -/
theorem associatedGradedExternalModule_scalarTower
    (hzero : ∀ (a : A) n (x : M n),
      (I.associatedGradedComponentMap 0 ⟨a, by simp⟩ : I.associatedGraded) •
          DirectSum.of M n x = DirectSum.of M n (a • x)) :
    IsScalarTower A I.associatedGraded (⨁ n, M n) := by
  have hbase (a : A) (x : ⨁ n, M n) :
      (algebraMap A I.associatedGraded a) • x = a • x := by
    induction x using DirectSum.induction_on with
    | zero => simp only [smul_zero]
    | of n x =>
      rw [← I.associatedGradedComponentMap_zero a, hzero, DirectSum.of_smul]
    | add x y hx hy => simp only [smul_add, hx, hy]
  refine ⟨fun a s x => ?_⟩
  have hs : (a • s : I.associatedGraded) = algebraMap A I.associatedGraded a * s :=
    Algebra.smul_def a s
  exact (congrArg (fun z : I.associatedGraded => z • x) hs).trans
    ((mul_smul (algebraMap A I.associatedGraded a) s x).trans (hbase a (s • x)))

end Ideal
