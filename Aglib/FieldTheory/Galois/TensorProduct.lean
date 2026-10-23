/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Separable.TensorProductSplitting
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! # Galois-indexed tensor evaluation

This is the native separable tensor splitting, reindexed by actual Galois
automorphisms. Its exact pure-tensor formula fixes the coordinates used for
finite Galois overlap and Cech cochain calculations.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IsGalois

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The canonical decomposition of a finite Galois self tensor product, indexed
by the original Galois group rather than by a replacement automorphism type. -/
def tensorProductEquivPi : L ⊗[K] L ≃ₐ[L] (Gal(L/K) → L) :=
  (Algebra.IsSeparable.tensorProductEquivPi K L L
    (Normal.splits (inferInstance : Normal K L))).trans
    (AlgEquiv.piCongrLeft' L (fun _ : L →ₐ[K] L => L)
      (algEquivEquivAlgHom K L).toEquiv.symm)

/-- The first tensor factor is the coefficient field; the Galois automorphism
acts on the second tensor factor. -/
@[simp]
theorem tensorProductEquivPi_tmul (a b : L) (σ : Gal(L/K)) :
    tensorProductEquivPi K L (a ⊗ₜ[K] b) σ = a * σ b := rfl

/-- The identity component is the ordinary multiplication map on pure tensors. -/
@[simp]
theorem tensorProductEquivPi_tmul_one (a b : L) :
    tensorProductEquivPi K L (a ⊗ₜ[K] b) 1 = a * b := rfl

end IsGalois
