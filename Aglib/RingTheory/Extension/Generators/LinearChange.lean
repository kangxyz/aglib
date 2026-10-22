/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Actual linear changes of algebra generators

The inverse is the native nonsingular inverse of the same coefficient matrix.
The new family is proved generating by recovering every original coordinate.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped Matrix

namespace Algebra.Generators

variable {R B n : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype n] [DecidableEq n]
variable (P : Generators R B n) (U : Matrix n n R)

/-- The actual linear combinations of the original generators. -/
def linearCoordinates : n → B := (algebraMap R B).mapMatrix U *ᵥ P.val

/-- Express the old polynomial variables in the new ones using the exact inverse matrix. -/
def inverseLinearSubstitution : MvPolynomial n R →ₐ[R] MvPolynomial n R :=
  aeval (C.mapMatrix U⁻¹ *ᵥ (X : n → MvPolynomial n R))

/-- Inverse substitution followed by evaluation recovers the original source point. -/
theorem aeval_comp_inverseLinearSubstitution (hU : IsUnit U.det) :
    (aeval (linearCoordinates P U)).comp (inverseLinearSubstitution U) = aeval P.val := by
  ext i
  simp only [AlgHom.comp_apply, inverseLinearSubstitution, aeval_X]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply,
    Matrix.map_apply, aeval_C, aeval_X]
  change ((algebraMap R B).mapMatrix U⁻¹ *ᵥ
    ((algebraMap R B).mapMatrix U *ᵥ P.val)) i = P.val i
  rw [Matrix.mulVec_mulVec, ← map_mul, Matrix.nonsing_inv_mul U hU,
    map_one, Matrix.one_mulVec]

/-- The transformed family is genuinely surjective as an algebra evaluation map. -/
theorem aeval_linearCoordinates_surjective (hU : IsUnit U.det) :
    Function.Surjective (aeval (R := R) (linearCoordinates P U)) := by
  intro b
  obtain ⟨f, hf⟩ := P.aeval_val_surjective b
  refine ⟨inverseLinearSubstitution U f, ?_⟩
  exact (DFunLike.congr_fun (aeval_comp_inverseLinearSubstitution P U hU) f).trans hf

/-- The actual transformed generating family, constructed from the proved surjectivity. -/
def linearChange (hU : IsUnit U.det) : Generators R B n :=
  Generators.ofSurjective (linearCoordinates P U) (aeval_linearCoordinates_surjective P U hU)

/-- The new generators are precisely the specified linear combinations. -/
@[simp] theorem linearChange_val (hU : IsUnit U.det) :
    (linearChange P U hU).val = linearCoordinates P U := rfl

/-- Inverse substitution takes exactly the original relation ideal back from the new one. -/
theorem comap_ker_inverseLinearSubstitution (hU : IsUnit U.det) :
    ((linearChange P U hU).ker).comap (inverseLinearSubstitution U).toRingHom = P.ker := by
  ext f
  simp only [Ideal.mem_comap, ker_eq_ker_aeval_val, RingHom.mem_ker]
  change aeval (linearCoordinates P U) (inverseLinearSubstitution U f) = 0 ↔ aeval P.val f = 0
  rw [← AlgHom.comp_apply, aeval_comp_inverseLinearSubstitution P U hU]

end Algebra.Generators
