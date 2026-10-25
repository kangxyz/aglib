/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Strata
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Original local lifts through one fixed global mono

Jointly faithful zero-preserving functors detect that the original arrow kills
the cokernel of a fixed mono. The native abelian lift then factors that same
arrow. In particular, actual open restrictions suffice; exactness of these
functors and a global coefficient-colimit theorem are not additional inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u v w

/-- Local lifts through the pullbacks of one fixed original mono give an
actual lift through that original mono. Exactness of the detecting functors
is not required. -/
theorem exists_factor_of_jointlyFaithful
    {C : Type u} [Category.{v} C] [Abelian C]
    {J : Type w} {D : J → Type*} [∀ j, Category (D j)]
    (L : ∀ j, C ⥤ D j) [∀ j, HasZeroMorphisms (D j)]
    [∀ j, (L j).PreservesZeroMorphisms] (hL : JointlyFaithful L)
    {A B F : C} (τ : A ⟶ B) [Mono τ] (α : F ⟶ B)
    (hlocal : ∀ j, ∃ β : (L j).obj F ⟶ (L j).obj A,
      β ≫ (L j).map τ = (L j).map α) :
    ∃ β : F ⟶ A, β ≫ τ = α := by
  have hz : α ≫ cokernel.π τ = 0 := by
    apply hL.map_injective
    intro j
    obtain ⟨β, hβ⟩ := hlocal j
    rw [(L j).map_comp, (L j).map_zero, ← hβ, Category.assoc,
      ← (L j).map_comp, cokernel.condition, (L j).map_zero, comp_zero]
  exact ⟨Abelian.monoLift τ α hz, Abelian.monoLift_comp τ α hz⟩

attribute [local instance] hasSheafifyLarge

/-- Original lifts on any actual open cover factor the original coefficient
arrow through one fixed global mono. -/
theorem exists_factor_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    {A B F : AbelianSheaf.{u, u + 1} X} (τ : A ⟶ B) [Mono τ] (α : F ⟶ B)
    (hlocal : ∀ j, ∃ β : (inverseImage (𝒰.f j)).obj F ⟶
      (inverseImage (𝒰.f j)).obj A,
      β ≫ (inverseImage (𝒰.f j)).map τ = (inverseImage (𝒰.f j)).map α) :
    ∃ β : F ⟶ A, β ≫ τ = α := by
  have hL : JointlyFaithful (fun j => inverseImage (𝒰.f j)) :=
    jointlyFaithful_immersionInverseImages 𝒰.X 𝒰.f
      (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)
  exact exists_factor_of_jointlyFaithful _ hL τ α hlocal

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
