/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Boundary
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Aglib.Algebra.Module.LinearMap.Exact.Diagram

/-!
# The canonical higher Serre pairing across a short exact presentation

The original Ext extension class and original cohomology connecting map form the two
rows. Over a field, native vector-space dual exactness and extension of linear functionals
transfer bijectivity of the canonical pairings to the quotient coefficient. Every map in
the diagram is the already defined Yoneda/trace pairing or original coefficient map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι]

/-- Extending linear functionals along the original injective cohomology connecting map
transfers surjectivity of the canonical pairing over a field. -/
theorem projectiveSerrePairing_surjective_of_shortExact
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace K ι).Modules) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 + j = n)
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace K ι) S.X₂) i))
    (h₁ : Function.Surjective (projectiveSerrePairing K ι n e S.X₁ (i + 1) j hij)) :
    Function.Surjective (projectiveSerrePairing K ι n e S.X₃ i (j + 1) (by omega)) := by
  let α : K →+* Γ((ProjectiveSpace K ι), ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₂ i
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₃ i
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₁ (i + 1)
  let δ := moduleCohomologyConnectingOfHom (ProjectiveSpace K ι) α S hS i
  have hδinj : Function.Injective δ := by
    let := hH
    exact (LinearMap.injective_iff_eq_zero_of_exact
      (moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace K ι) α S hS i)).mpr
        (Subsingleton.elim _ _)
  intro x
  obtain ⟨y, hy⟩ := LinearMap.dualMap_surjective_of_injective hδinj x
  obtain ⟨z, hz⟩ := h₁ y
  refine ⟨hS.extClass.comp z (show 1 + j = j + 1 by omega), ?_⟩
  ext t
  rw [projectiveSerrePairing_connecting K ι n e S hS i j hij]
  change (projectiveSerrePairing K ι n e S.X₁ (i + 1) j hij z) (δ t) = x t
  rw [hz]
  exact DFunLike.congr_fun hy t

/-- The original right exact Ext and dual-cohomology rows transfer bijectivity of the
canonical pairings across an actual short exact presentation. -/
theorem projectiveSerrePairing_bijective_of_shortExact
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace K ι).Modules) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 + j = n)
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace K ι) S.X₂) i))
    (hE : Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      S.X₂ (twistingSheaf K ι (-(Fintype.card ι : ℤ))) (j + 1)))
    (h₂ : Function.Bijective (projectiveSerrePairing K ι n e S.X₂ (i + 1) j hij))
    (h₁ : Function.Bijective (projectiveSerrePairing K ι n e S.X₁ (i + 1) j hij)) :
    Function.Bijective (projectiveSerrePairing K ι n e S.X₃ i (j + 1) (by omega)) := by
  let α : K →+* Γ((ProjectiveSpace K ι), ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₂ i
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₃ i
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₁ (i + 1)
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₂ (i + 1)
  let ω := twistingSheaf K ι (-(Fintype.card ι : ℤ))
  let δ := moduleCohomologyConnectingOfHom (ProjectiveSpace K ι) α S hS i
  let f := moduleCohomologyMapOfHom (ProjectiveSpace K ι) α S.f (i + 1)
  let p₁ := projectiveSerrePairing K ι n e S.X₁ (i + 1) j hij
  let p₂ := projectiveSerrePairing K ι n e S.X₂ (i + 1) j hij
  let p₃ := projectiveSerrePairing K ι n e S.X₃ i (j + 1) (by omega)
  let ε := (Ext.mk₀ (C := (ProjectiveSpace K ι).Modules) S.f).precompOfLinear K ω (Nat.zero_add j)
  let Δ := hS.extClass.precompOfLinear (C := (ProjectiveSpace K ι).Modules)
    K ω (show 1 + j = j + 1 by omega)
  have hεδ : Function.Exact ε Δ :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₁' (C := (ProjectiveSpace K ι).Modules)
        hS ω j (j + 1) (by omega))
  have hδf : Function.Exact δ f :=
    moduleCohomologyConnectingOfHom_exact_right (ProjectiveSpace K ι) α S hS i
  have hdual : Function.Exact f.dualMap δ.dualMap := by
    rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker, hδf.linearMap_ker_eq]
  have hδinj : Function.Injective δ := by
    let := hH
    exact (LinearMap.injective_iff_eq_zero_of_exact
      (moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace K ι) α S hS i)).mpr
        (Subsingleton.elim _ _)
  have hΔsurj : Function.Surjective Δ := by
    intro x
    exact Ext.contravariant_sequence_exact₃ (C := (ProjectiveSpace K ι).Modules)
      hS ω x (hE.elim _ 0)
      (show 1 + j = j + 1 by omega)
  apply LinearMap.bijective_of_rightExact_diagram ε Δ f.dualMap δ.dualMap p₂ p₁ p₃
    hεδ hdual hΔsurj (LinearMap.dualMap_surjective_of_injective hδinj) _ _ h₂.2 h₁
  · ext y x
    exact projectiveSerrePairing_naturality K ι n e S.f (i + 1) j hij y x
  · ext y x
    exact projectiveSerrePairing_connecting K ι n e S hS i j hij y x

end AlgebraicGeometry.Scheme.Cohomology
