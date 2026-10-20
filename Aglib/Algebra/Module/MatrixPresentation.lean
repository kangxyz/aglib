/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Finite projective modules as actual matrix images

The original finite-free inclusion and retraction give an idempotent matrix and a literal
image-module equivalence. Matrices of a specified overlap equivalence retain both inclusions
and satisfy the original rectangular projector identities.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Module/MatrixPresentation.lean` from the supplied
frozen Quillen snapshot.
SHA-256: `6e071fb4bdb849ce450682c5ed82e7c1df8a1b79a16b03c0b45779b125c8252b`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct Matrix
universe u v w
namespace Module.Projective
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {n : ℕ} (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M)

/-- The literal finite matrix of the inclusion followed by the retraction. -/
def retractMatrix : Matrix (Fin n) (Fin n) R := LinearMap.toMatrix' (i.comp r)

/-- The original projector matrix acts by the given inclusion and retraction. -/
theorem retractMatrix_apply (x : Fin n → R) : (retractMatrix i r).mulVecLin x = i (r x) :=
  LinearMap.toMatrix'_mulVec (i.comp r) x

/-- An actual splitting gives an idempotent matrix, with no freeness hypothesis on the
retract. -/
theorem retractMatrix_idempotent (h : r.comp i = LinearMap.id) :
    retractMatrix i r * retractMatrix i r = retractMatrix i r := by
  unfold retractMatrix
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro x
  change i (r (i (r x))) = i (r x)
  rw [show r (i (r x)) = r x from LinearMap.congr_fun h (r x)]

/-- The actual retract is linearly equivalent to the range of its original finite matrix. -/
def retractMatrixImageIso (h : r.comp i = LinearMap.id) :
    M ≃ₗ[R] LinearMap.range (retractMatrix i r).mulVecLin where
  toFun x := ⟨i x, ⟨i x, by rw [retractMatrix_apply, show r (i x) = x from
    LinearMap.congr_fun h x]⟩⟩
  invFun x := r x.val
  left_inv x := LinearMap.congr_fun h x
  right_inv x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change i (r x.val) = x.val
    rw [← hy, retractMatrix_apply]
    rw [show r (i (r y)) = r y from LinearMap.congr_fun h (r y)]
  map_add' x y := by apply Subtype.ext; exact map_add i x y
  map_smul' a x := by apply Subtype.ext; exact map_smul i a x

/-- The image equivalence retains the original inclusion. -/
theorem retractMatrixImageIso_apply (h : r.comp i = LinearMap.id) (x : M) :
    (retractMatrixImageIso i r h x).val = i x := rfl

/-- The inverse image equivalence retains the original retraction. -/
theorem retractMatrixImageIso_symm_apply (h : r.comp i = LinearMap.id)
    (x : LinearMap.range (retractMatrix i r).mulVecLin) :
    (retractMatrixImageIso i r h).symm x = r x.val := rfl

variable (R M) in
/-- Every finite projective module has an actual finite matrix-image presentation. -/
theorem exists_retractMatrixImageIso [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M)
      (_h : r.comp i = LinearMap.id),
      retractMatrix i r * retractMatrix i r = retractMatrix i r ∧
      Nonempty (M ≃ₗ[R] LinearMap.range (retractMatrix i r).mulVecLin) := by
  obtain ⟨n, r, i, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨n, i, r, h, retractMatrix_idempotent i r h, ⟨retractMatrixImageIso i r h⟩⟩

end Module.Projective

namespace Module.Projective
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] {m n : ℕ}
variable (i : M →ₗ[R] Fin m → R) (r : (Fin m → R) →ₗ[R] M)
  (j : N →ₗ[R] Fin n → R) (s : (Fin n → R) →ₗ[R] N)
  (e : N ≃ₗ[R] M)

/-- The matrix of the original overlap equivalence between specified finite-free retractions. -/
def transitionMatrix : Matrix (Fin m) (Fin n) R :=
  LinearMap.toMatrix' (i.comp (e.toLinearMap.comp s))

/-- The overlap matrix acts by the original retraction, equivalence and inclusion. -/
theorem transitionMatrix_apply (x : Fin n → R) :
    transitionMatrix i s e *ᵥ x = i (e (s x)) :=
  LinearMap.toMatrix'_mulVec _ _

/-- The transition matrix intertwines the original module inclusions and equivalence. -/
theorem transitionMatrix_inclusion (hs : s.comp j = LinearMap.id) (x : N) :
    transitionMatrix i s e *ᵥ j x = i (e x) := by
  rw [transitionMatrix_apply, show s (j x) = x from LinearMap.congr_fun hs x]

/-- The two opposite transition matrices compose to the literal projector. -/
theorem transitionMatrix_mul_inverse (hs : s.comp j = LinearMap.id) :
    transitionMatrix i s e * transitionMatrix j r e.symm = retractMatrix i r := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (transitionMatrix i s e * transitionMatrix j r e.symm) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, transitionMatrix_apply, transitionMatrix_apply]
  change i (e (s (j (e.symm (r x))))) = (retractMatrix i r).mulVecLin x
  rw [show s (j (e.symm (r x))) = e.symm (r x) from LinearMap.congr_fun hs _]
  rw [LinearEquiv.apply_symm_apply, retractMatrix_apply]

/-- The target projector fixes the original rectangular transition matrix. -/
theorem retractMatrix_mul_transition (hr : r.comp i = LinearMap.id) :
    retractMatrix i r * transitionMatrix i s e = transitionMatrix i s e := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (retractMatrix i r * transitionMatrix i s e) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, transitionMatrix_apply, Matrix.toLin'_apply,
    transitionMatrix_apply]
  change (retractMatrix i r).mulVecLin (i (e (s x))) = i (e (s x))
  rw [retractMatrix_apply, show r (i (e (s x))) = e (s x) from LinearMap.congr_fun hr _]

/-- The original transition matrix factors through its source projector. -/
theorem transitionMatrix_mul_retract (hs : s.comp j = LinearMap.id) :
    transitionMatrix i s e * retractMatrix j s = transitionMatrix i s e := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (transitionMatrix i s e * retractMatrix j s) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, transitionMatrix_apply, Matrix.toLin'_apply,
    transitionMatrix_apply]
  change i (e (s ((retractMatrix j s).mulVecLin x))) = i (e (s x))
  rw [retractMatrix_apply, show s (j (s x)) = s x from LinearMap.congr_fun hs _]

end Module.Projective
