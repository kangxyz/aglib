/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Coordinates and relation witnesses after tensoring a finite presentation

The coefficient module need not be free, and the tensor factor need not be flat.
The surjectivity of the presentation is precisely the hypothesis needed for
right exactness of tensor product.
-/

@[expose] public noncomputable section

open TensorProduct LinearMap
open scoped BigOperators

namespace Module.FinitePresentation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (T : Type*) [AddCommGroup T] [Module R T]
variable {d r : ℕ}

/-- Interpret a finite vector as coordinates for a tensor with a presented module. -/
def tensorCoordinates (f : (Fin d → R) →ₗ[R] M) :
    (Fin d → T) →ₗ[R] T ⊗[R] M :=
  (f.lTensor T).comp (TensorProduct.piScalarRight R R T (Fin d)).symm.toLinearMap

/-- The relations of a finite presentation, in actual finite-vector coordinates. -/
def tensorRelations (g : (Fin r → R) →ₗ[R] (Fin d → R)) :
    (Fin r → T) →ₗ[R] (Fin d → T) :=
  (TensorProduct.piScalarRight R R T (Fin d)).toLinearMap.comp
    (tensorCoordinates T g)

@[simp] theorem tensorCoordinates_single (f : (Fin d → R) →ₗ[R] M)
    (a : Fin d) (t : T) :
    tensorCoordinates T f (Pi.single a t) = t ⊗ₜ[R] f (Pi.single a 1) := by
  simp [tensorCoordinates]

/-- The coordinate map is the genuine finite sum of pure tensors. -/
theorem tensorCoordinates_apply (f : (Fin d → R) →ₗ[R] M) (z : Fin d → T) :
    tensorCoordinates T f z = ∑ a, z a ⊗ₜ[R] f (Pi.single a 1) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single z]
  simp

/-- The matrix of the relations is obtained from the original presentation map. -/
theorem tensorRelations_apply (g : (Fin r → R) →ₗ[R] (Fin d → R))
    (w : Fin r → T) (a : Fin d) :
    tensorRelations T g w a = ∑ b, g (Pi.single b 1) a • w b := by
  classical
  simp [tensorRelations, tensorCoordinates_apply, TensorProduct.piScalarRight_apply]

/-- Surjectivity survives arbitrary scalar extension. -/
theorem tensorCoordinates_surjective (f : (Fin d → R) →ₗ[R] M)
    (hf : Function.Surjective f) : Function.Surjective (tensorCoordinates T f) :=
  (LinearMap.lTensor_surjective T hf).comp
    (TensorProduct.piScalarRight R R T (Fin d)).symm.surjective

/-- Every formal coordinate relation has actual finite relation witnesses. -/
theorem tensorCoordinates_eq_zero_iff
    (f : (Fin d → R) →ₗ[R] M) (g : (Fin r → R) →ₗ[R] (Fin d → R))
    (hf : Function.Surjective f) (hgf : Function.Exact g f) (z : Fin d → T) :
    tensorCoordinates T f z = 0 ↔ ∃ w : Fin r → T, tensorRelations T g w = z := by
  let ed := TensorProduct.piScalarRight R R T (Fin d)
  let er := TensorProduct.piScalarRight R R T (Fin r)
  have he := lTensor_exact T hgf hf
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (he (ed.symm z)).mp hz
    refine ⟨er w, ?_⟩
    change ed ((g.lTensor T) (er.symm (er w))) = z
    rw [er.symm_apply_apply, hw, ed.apply_symm_apply]
  · rintro ⟨w, rfl⟩
    change (f.lTensor T)
      (ed.symm (ed ((g.lTensor T) (er.symm w)))) = 0
    rw [ed.symm_apply_apply]
    exact he.apply_apply_eq_zero _

/-- A finite module over a Noetherian ring supplies a genuine presentation whose
coordinates and relation witnesses remain valid over every scalar module. -/
theorem exists_tensor_presentation [IsNoetherianRing R] [Module.Finite R M] :
    ∃ (d r : ℕ) (f : (Fin d → R) →ₗ[R] M)
      (g : (Fin r → R) →ₗ[R] (Fin d → R)),
      Function.Surjective f ∧ Function.Exact g f ∧
      Function.Surjective (tensorCoordinates T f) ∧
      ∀ z : Fin d → T, tensorCoordinates T f z = 0 ↔
        ∃ w : Fin r → T, tensorRelations T g w = z := by
  let := Module.finitePresentation_of_finite R M
  obtain ⟨d, r, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  exact ⟨d, r, f, g, hf, hgf, tensorCoordinates_surjective T f hf,
    tensorCoordinates_eq_zero_iff T f g hf hgf⟩

end Module.FinitePresentation
