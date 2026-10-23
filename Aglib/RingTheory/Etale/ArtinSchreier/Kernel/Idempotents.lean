/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ArtinSchreier.Kernel
public import Mathlib.RingTheory.Idempotents

/-!
# Canonical idempotents of an Artin--Schreier root

Evaluate the inverse kernel-algebra equivalence's coordinate idempotents at
the original root `b`. The resulting actual elements form a complete
orthogonal family and cut `b` into the literal residue constants. Every
statement includes the zero ring; only the equation `p = 0` is used for the base.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.ArtinSchreier

variable {R : Type*} [CommRing R] (p : ℕ)

/-- Evaluation of the original quotient algebra at the given original root. -/
def kernelRootEvaluation (b : R) (hb : b ^ p - b = 0) :
    RootAlgebra p (0 : R) →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (poly p (0 : R)) (Algebra.ofId R R) b (by
    simpa only [poly, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_zero, map_zero, sub_zero] using hb)

/-- The original quotient root evaluates to the specified element `b`. -/
@[simp]
theorem kernelRootEvaluation_root (b : R) (hb : b ^ p - b = 0) :
    kernelRootEvaluation p b hb (AdjoinRoot.root (poly p (0 : R))) = b := by
  simp only [kernelRootEvaluation, AdjoinRoot.liftAlgHom_root]

variable [Fact p.Prime] (hR : (p : R) = 0) (b : R) (hb : b ^ p - b = 0)

/-- Transport the original root evaluation through the canonical product splitting. -/
def kernelCoordinateEvaluation : (ZMod p → R) →ₐ[R] R :=
  (kernelRootEvaluation p b hb).comp (kernelAlgEquiv p hR).symm.toAlgHom

/-- The canonical idempotent for a residue constant, evaluated at the original root. -/
def rootIdempotent (i : ZMod p) : R :=
  kernelRootEvaluation p b hb ((kernelAlgEquiv p hR).symm (Pi.single i 1))

/-- The literal coordinate function evaluates to the original root. -/
theorem kernelCoordinateEvaluation_residue :
    kernelCoordinateEvaluation p hR b hb (fun i : ZMod p => (i.val : R)) = b := by
  have h : (fun i : ZMod p => (i.val : R)) =
      kernelAlgEquiv p hR (AdjoinRoot.root (poly p (0 : R))) := by
    funext i
    exact (kernelAlgEquiv_root p hR i).symm
  rw [h]
  change kernelRootEvaluation p b hb
    ((kernelAlgEquiv p hR).symm
      (kernelAlgEquiv p hR (AdjoinRoot.root (poly p (0 : R))))) = b
  rw [AlgEquiv.symm_apply_apply, kernelRootEvaluation_root]

/-- The actual root idempotents form a complete orthogonal family. -/
theorem rootIdempotents_completeOrthogonal :
    CompleteOrthogonalIdempotents (rootIdempotent p hR b hb) := by
  change CompleteOrthogonalIdempotents
    ((kernelCoordinateEvaluation p hR b hb).toRingHom ∘
      fun i : ZMod p => Pi.single i (1 : R))
  exact (CompleteOrthogonalIdempotents.single (fun _ : ZMod p => R)).map _

/-- The canonical root idempotents sum to one, including in the zero ring. -/
theorem sum_rootIdempotent : ∑ i : ZMod p, rootIdempotent p hR b hb i = 1 :=
  (rootIdempotents_completeOrthogonal p hR b hb).complete

/-- Every canonical root component is idempotent. -/
theorem rootIdempotent_sq (i : ZMod p) :
    rootIdempotent p hR b hb i ^ 2 = rootIdempotent p hR b hb i := by
  simpa only [pow_two] using ((rootIdempotents_completeOrthogonal p hR b hb).idem i).eq

/-- Distinct residue components are orthogonal. -/
theorem rootIdempotent_mul_of_ne {i j : ZMod p} (hij : i ≠ j) :
    rootIdempotent p hR b hb i * rootIdempotent p hR b hb j = 0 :=
  (rootIdempotents_completeOrthogonal p hR b hb).ortho hij

/-- On the actual idempotent component, the original root is its indicated residue constant. -/
theorem rootIdempotent_mul_root (i : ZMod p) :
    rootIdempotent p hR b hb i * b = (i.val : R) * rootIdempotent p hR b hb i := by
  classical
  let F := kernelCoordinateEvaluation p hR b hb
  let δ : ZMod p → R := Pi.single i 1
  let c : ZMod p → R := fun j => (j.val : R)
  have h : δ * c = algebraMap R (ZMod p → R) (i.val : R) * δ := by
    ext j
    by_cases hij : i = j
    · subst j
      simp [δ, c]
    · simp [δ, c, hij]
  calc
    rootIdempotent p hR b hb i * b = F (δ * c) := by
      rw [map_mul]
      have hc : F c = b := kernelCoordinateEvaluation_residue p hR b hb
      rw [hc]
      rfl
    _ = F (algebraMap R (ZMod p → R) (i.val : R) * δ) := congrArg F h
    _ = (i.val : R) * rootIdempotent p hR b hb i := by
      rw [map_mul, AlgHom.commutes]
      rfl

end Algebra.ArtinSchreier
