/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Pi

/-! # Iterated Galois tensor coordinates for low-degree cochains

Repeated native tensor splitting produces cumulative inhomogeneous Galois
coordinates. Function arguments are stored from the innermost to the outermost
tensor factor, so the formulas below explicitly name their order. No new
cohomology groups or cocycle predicates are introduced.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IsGalois

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Coordinates on the triple tensor product, evaluated in argument order tau, sigma. -/
def tripleTensorEquivPi : L ⊗[K] (L ⊗[K] L) ≃ₐ[L] (Gal(L/K) → Gal(L/K) → L) := by
  classical
  let := Fintype.ofFinite (Gal(L/K))
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    ((tensorProductEquivPi K L).restrictScalars K)).trans
      ((Algebra.TensorProduct.piRight K L L (fun _ : Gal(L/K) => L)).trans
        (AlgEquiv.piCongrRight fun _ => tensorProductEquivPi K L))

/-- These are exactly the cumulative coordinates used for inhomogeneous two-cochains. -/
@[simp]
theorem tripleTensorEquivPi_tmul (a b c : L) (σ τ : Gal(L/K)) :
    tripleTensorEquivPi K L (a ⊗ₜ[K] (b ⊗ₜ[K] c)) τ σ =
      a * σ b * (σ * τ) c := by
  classical
  simp [tripleTensorEquivPi, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_mul, mul_assoc]

/-- Coordinates on the fourfold tensor product, evaluated in order upsilon, tau, sigma. -/
def quadrupleTensorEquivPi : L ⊗[K] (L ⊗[K] (L ⊗[K] L)) ≃ₐ[L]
    (Gal(L/K) → Gal(L/K) → Gal(L/K) → L) := by
  classical
  let := Fintype.ofFinite (Gal(L/K))
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    ((tripleTensorEquivPi K L).restrictScalars K)).trans
      ((Algebra.TensorProduct.piRight K L L
        (fun _ : Gal(L/K) => Gal(L/K) → L)).trans
        (AlgEquiv.piCongrRight fun _ =>
          (Algebra.TensorProduct.piRight K L L (fun _ : Gal(L/K) => L)).trans
            (AlgEquiv.piCongrRight fun _ => tensorProductEquivPi K L)))

/-- The fourfold coordinates retain the original cumulative product convention. -/
@[simp]
theorem quadrupleTensorEquivPi_tmul (a b c d : L) (σ τ υ : Gal(L/K)) :
    quadrupleTensorEquivPi K L (a ⊗ₜ[K] (b ⊗ₜ[K] (c ⊗ₜ[K] d))) υ τ σ =
      a * σ b * (σ * τ) c * (σ * τ * υ) d := by
  classical
  simp [quadrupleTensorEquivPi, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_mul, mul_assoc]

end IsGalois
