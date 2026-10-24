/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Linear connecting maps on original module-sheaf cohomology

The native `Sheaf.H.δ` for an actual short exact sequence of constant-ring
module sheaves is linear for the unchanged `cohomologyModule` actions.
Linearity is the native connecting-map naturality equation for the actual
short-complex endomorphism given by scalar multiplication on all three terms.
Both adjacent exact pairs retain the original coefficient and connecting maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify cohomologyModule

/-- The original connecting homomorphism is linear for the unchanged cohomology action. -/
def cohomologyδLinearMap (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    CategoryTheory.Sheaf.H.{e} ((underlying R J).obj S.X₃) q₀ →ₗ[R]
      CategoryTheory.Sheaf.H.{e} ((underlying R J).obj S.X₁) q₁ where
  toAddHom :=
    (CategoryTheory.Sheaf.H.δ (hS.map_of_exact (underlying R J)) q₀ q₁ h).toAddHom
  map_smul' r x := by
    let φ : S ⟶ S := {
      τ₁ := r • 𝟙 S.X₁
      τ₂ := r • 𝟙 S.X₂
      τ₃ := r • 𝟙 S.X₃
      comm₁₂ := by simp
      comm₂₃ := by simp }
    exact CategoryTheory.Sheaf.H.δ_naturality q₀ q₁ h
      (hS.map_of_exact (underlying R J)) (hS.map_of_exact (underlying R J))
      ((underlying R J).mapShortComplex.map φ) x

/-- The original linear connecting map as a morphism of the canonical module objects. -/
def cohomologyδ (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    (cohomology J R q₀).obj S.X₃ ⟶ (cohomology J R q₁).obj S.X₁ :=
  ModuleCat.ofHom
    (X := CategoryTheory.Sheaf.H.{e} ((underlying R J).obj S.X₃) q₀)
    (Y := CategoryTheory.Sheaf.H.{e} ((underlying R J).obj S.X₁) q₁)
    (cohomologyδLinearMap J R S hS q₀ q₁ h)

/-- Forgetting linearity gives the literal native additive connecting homomorphism. -/
@[simp]
theorem cohomologyδ_hom_toAddMonoidHom
    (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    (cohomologyδ J R S hS q₀ q₁ h).hom.toAddMonoidHom =
      CategoryTheory.Sheaf.H.δ (hS.map_of_exact (underlying R J)) q₀ q₁ h := rfl

/-- The linear connecting map acts by the unchanged original `Sheaf.H.δ`. -/
@[simp]
theorem cohomologyδ_apply (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁)
    (x : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj S.X₃) q₀) :
    cohomologyδ J R S hS q₀ q₁ h x =
      CategoryTheory.Sheaf.H.δ (hS.map_of_exact (underlying R J)) q₀ q₁ h x := rfl

/-- Connecting-map naturality as an equality of actual module morphisms. -/
theorem cohomologyδ_naturality
    {S T : ShortComplex (Sheaf J (ModuleCat.{max u v} R))}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    (cohomology J R q₀).map φ.τ₃ ≫ cohomologyδ J R T hT q₀ q₁ h =
      cohomologyδ J R S hS q₀ q₁ h ≫ (cohomology J R q₁).map φ.τ₁ := by
  ext x
  exact CategoryTheory.Sheaf.H.δ_naturality q₀ q₁ h
    (hS.map_of_exact (underlying R J)) (hT.map_of_exact (underlying R J))
    ((underlying R J).mapShortComplex.map φ) x

/-- Exactness immediately before the original linear connecting map. -/
theorem cohomologyδ_exact_left (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    Function.Exact ((cohomology J R q₀).map S.g).hom
      (cohomologyδ J R S hS q₀ q₁ h).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (CategoryTheory.Sheaf.H.longSequence_exact₃'
      (hS.map_of_exact (underlying R J)) q₀ q₁ h)

/-- Exactness immediately after the original linear connecting map. -/
theorem cohomologyδ_exact_right (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q₀ q₁ : ℕ) (h : q₀ + 1 = q₁) :
    Function.Exact (cohomologyδ J R S hS q₀ q₁ h).hom
      ((cohomology J R q₁).map S.f).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (CategoryTheory.Sheaf.H.longSequence_exact₁'
      (hS.map_of_exact (underlying R J)) q₀ q₁ h)

end ModuleCat.Sheaf
