/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Polynomial.Module.TensorProduct

/-!
# The Rees module as the actual image of scalar extension

The canonical map from the Rees scalar extension of a module to its
polynomial module has image equal to the native submodule of its adic
filtration. No flatness, finiteness, or Noetherian hypothesis is needed.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct PolynomialModule
universe u v

namespace reesAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A)
  (M : Type v) [AddCommGroup M] [Module A M]

/-- The original scalar extension map to polynomial coefficients. -/
def moduleImageMap : reesAlgebra I ⊗[A] M →ₗ[reesAlgebra I] PolynomialModule A M :=
  (PolynomialModule.lsingle A 0).liftBaseChange (reesAlgebra I)

@[simp]
theorem moduleImageMap_tmul (b : reesAlgebra I) (m : M) :
    moduleImageMap I M (b ⊗ₜ[A] m) = b • PolynomialModule.single A 0 m := rfl

/-- The image is exactly the polynomial-module Rees submodule of the adic filtration. -/
theorem range_moduleImageMap :
    LinearMap.range (moduleImageMap I M) =
      (I.stableFiltration (⊤ : Submodule A M)).submodule := by
  let F := I.stableFiltration (⊤ : Submodule A M)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      apply F.submodule.smul_mem b
      intro n
      change (PolynomialModule.single A 0 m).coeff n ∈ I ^ n • (⊤ : Submodule A M)
      by_cases hn : n = 0
      · subst n
        simp
      · simp [PolynomialModule.coeff_single, Ne.symm hn]
    | add x y hx hy => simpa only [map_add] using F.submodule.add_mem hx hy
  · rw [← F.submodule_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨n, rfl⟩, m, hm, rfl⟩
    change m ∈ I ^ n • (⊤ : Submodule A M) at hm
    refine Submodule.smul_induction_on hm (fun a ha m hm => ?_) (fun x y hx hy => ?_)
    · refine ⟨(⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I)
        ⊗ₜ[A] m, ?_⟩
      change Polynomial.monomial n a • PolynomialModule.single A 0 m =
        PolynomialModule.single A n (a • m)
      simp only [PolynomialModule.monomial_smul_single, add_zero]
    · rw [PolynomialModule.single_add]
      exact (LinearMap.range (moduleImageMap I M)).add_mem hx hy

end reesAlgebra
