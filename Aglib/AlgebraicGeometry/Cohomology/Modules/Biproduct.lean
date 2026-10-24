/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Length

/-!
# Finite biproducts on original structural cohomology

The additive coefficient functor preserves finite biproducts. Its native
comparison gives a linear equivalence from the original cohomology of the
module-sheaf biproduct to the finite product of original cohomology modules,
for the same specified structural scalar map. The resulting length formula
is used by the finite trace-coordinate surface bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem finiteCopies_length {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : ℕ) :
    Module.length R (Fin r → M) = (r : ℕ∞) * Module.length R M := by
  rw [Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤)) (n : ℕ)

/-- The native finite-biproduct comparison, retaining the original
cohomology objects and their specified structural scalar actions. -/
def moduleCohomologyBiproductLinearEquiv {ι : Type} [Fintype ι]
    (M : ι → X.Modules) :
    letI := moduleCohomologyModuleOfHom X α (⨁ M) n
    letI : ∀ i, Module R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) n
    Sheaf.H.{u + 1} (moduleAddSheaf X (⨁ M)) n ≃ₗ[R]
      ∀ i, Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n := by
  letI := moduleCohomologyModuleOfHom X α (⨁ M) n
  letI : ∀ i, Module R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) n
  let F : X.Modules ⥤ ModuleCat.{u + 1} R := moduleCohomologyFunctorOfHom X α n
  let : F.Additive := moduleCohomologyFunctorOfHom_additive X α n
  let : PreservesBiproduct M F := inferInstance
  let N : ι → ModuleCat.{u + 1} R := F.obj ∘ M
  let e : F.obj (⨁ M) ≅ ModuleCat.of R (∀ i, N i) :=
    F.mapBiproduct M ≪≫ biproduct.isoProduct N ≪≫ ModuleCat.piIsoPi.{u, 0, u + 1} N
  exact e.toLinearEquiv

/-- Length is additive on the original finite-biproduct coefficient. -/
theorem moduleCohomologyBiproduct_length {ι : Type} [Fintype ι]
    (M : ι → X.Modules) :
    letI := moduleCohomologyModuleOfHom X α (⨁ M) n
    letI : ∀ i, Module R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) n
    Module.length R (Sheaf.H.{u + 1} (moduleAddSheaf X (⨁ M)) n) =
      ∑ i, Module.length R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n) := by
  let := moduleCohomologyModuleOfHom X α (⨁ M) n
  let : ∀ i, Module R (Sheaf.H.{u + 1} (moduleAddSheaf X (M i)) n) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) n
  exact (moduleCohomologyBiproductLinearEquiv X α n M).length_eq.trans
    (Module.length_pi_of_fintype R _)

/-- A finite constant biproduct contributes its original number of copies. -/
theorem moduleCohomologyFiniteCopies_length (M : X.Modules) (r : ℕ) :
    letI := moduleCohomologyModuleOfHom X α (⨁ fun _ : Fin r => M) n
    letI := moduleCohomologyModuleOfHom X α M n
    Module.length R
        (Sheaf.H.{u + 1} (moduleAddSheaf X (⨁ fun _ : Fin r => M)) n) =
      (r : ℕ∞) * Module.length R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α (⨁ fun _ : Fin r => M) n
  exact (moduleCohomologyBiproductLinearEquiv X α n (fun _ : Fin r => M)).length_eq.trans
    (finiteCopies_length r)

end AlgebraicGeometry.Scheme.Cohomology
