/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite external graded modules generated in degree zero

The external action is transported through the original decomposition of the
associated graded ring. The degree-zero tensor presentation uses the actual
supplied compatible scalar action. Homogeneous generation is an explicit
intermediate hypothesis; it is not an algebraization assumption.
-/

@[expose] public noncomputable section

open DirectSum
open scoped TensorProduct
universe u v w
namespace Ideal
variable {A : Type u} [CommRing A] (I : Ideal A)
  (M : ℕ → Type v) [∀ n, AddCommGroup (M n)]

/-- The native external graded action transported through the actual ring
homogeneous decomposition. -/
@[instance_reducible]
def associatedGradedExternalModule
    [DirectSum.Gmodule (fun n => I.associatedGradedGrading n) M] :
    Module I.associatedGraded (⨁ n, M n) :=
  Module.compHom _ (DirectSum.decomposeRingEquiv I.associatedGradedGrading).toRingHom

/-- Transport retains the original homogeneous action on pure components. -/
lemma associatedGradedExternalModule_smul
    [DirectSum.Gmodule (fun n => I.associatedGradedGrading n) M]
    (r n : ℕ) (a : I.associatedGradedGrading r) (x : M n) :
    let := I.associatedGradedExternalModule M
    (a : I.associatedGraded) • DirectSum.of M n x =
      DirectSum.of M (r + n)
        (GradedMonoid.GSMul.smul (A := fun n => ↥(I.associatedGradedGrading n))
          (M := M) a x) := by
  let := I.associatedGradedExternalModule M
  change DirectSum.decompose I.associatedGradedGrading (a : I.associatedGraded) •
    DirectSum.of M n x = _
  rw [DirectSum.decompose_coe]
  exact DirectSum.Gmodule.of_smul_of (fun n => ↥(I.associatedGradedGrading n)) M a x

end Ideal

namespace GradedModule
variable {B : Type u} [CommRing B] (R : Type w) [CommRing R] [Algebra B R]
  (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)]
  [Module R (⨁ n, M n)] [IsScalarTower B R (⨁ n, M n)]

/-- The actual degree-zero scalar-extension presentation of an external module.
The base can be an affine coordinate ring, not just the original global base. -/
def degreeZeroTensorMap : R ⊗[B] M 0 →ₗ[R] (⨁ n, M n) :=
  (DirectSum.lof B ℕ M 0).liftBaseChange R

@[simp]
lemma degreeZeroTensorMap_tmul (a : R) (x : M 0) :
    degreeZeroTensorMap (B := B) R M (a ⊗ₜ[B] x) = a • DirectSum.lof B ℕ M 0 x := rfl

/-- Homogeneous degree-zero generation makes the original tensor presentation
surjective. Only the actual homogeneous coefficient family and action are used. -/
theorem degreeZeroTensorMap_surjective (G : ℕ → Submodule B R)
    (hgen : ∀ n (x : M n), DirectSum.lof B ℕ M n x ∈
      Submodule.span B {z : ⨁ n, M n | ∃ a : G n, ∃ y : M 0,
        z = (a : R) • DirectSum.lof B ℕ M 0 y}) :
    Function.Surjective (degreeZeroTensorMap (B := B) R M) := by
  let P := LinearMap.range (degreeZeroTensorMap (B := B) R M)
  have hzero (y : M 0) : DirectSum.lof B ℕ M 0 y ∈ P := by
    refine ⟨1 ⊗ₜ[B] y, ?_⟩
    simp only [degreeZeroTensorMap_tmul, one_smul]
  have hcomponent (n : ℕ) (x : M n) : DirectSum.lof B ℕ M n x ∈ P := by
    have hle : Submodule.span B
        {z : ⨁ n, M n | ∃ a : G n, ∃ y : M 0,
          z = (a : R) • DirectSum.lof B ℕ M 0 y} ≤
        P.restrictScalars B := by
      apply Submodule.span_le.mpr
      rintro z ⟨a, y, rfl⟩
      exact P.smul_mem (a : R) (hzero y)
    exact hle (hgen n x)
  intro x
  change x ∈ P
  induction x using DirectSum.induction_on with
  | zero => exact P.zero_mem
  | of n x => exact hcomponent n x
  | add x y hx hy => exact P.add_mem hx hy

/-- Finite degree zero over the actual coefficient base and homogeneous
generation imply finiteness over the full acting ring. -/
theorem finite_of_degreeZero_generation [Module.Finite B (M 0)]
    (G : ℕ → Submodule B R)
    (hgen : ∀ n (x : M n), DirectSum.lof B ℕ M n x ∈
      Submodule.span B {z : ⨁ n, M n | ∃ a : G n, ∃ y : M 0,
        z = (a : R) • DirectSum.lof B ℕ M 0 y}) :
    Module.Finite R (⨁ n, M n) :=
  Module.Finite.of_surjective (degreeZeroTensorMap (B := B) R M)
    (degreeZeroTensorMap_surjective (B := B) R M G hgen)

end GradedModule
