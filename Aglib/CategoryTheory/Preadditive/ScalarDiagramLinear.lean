/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Preadditive.ScalarDiagram
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Genuine index-linearity of an original scalar diagram

The coefficient ring may be arbitrary for additive index maps. Linearity in
the index category is asserted only for a commutative auxiliary ring and only
when the actual coefficient action equals the image of its scalar identities.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
universe u v i j w r
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I : Type i} [Category.{j} I] [Preadditive I]
  (H : C ⥤ I ⥤ AddCommGrpCat.{w}) [H.Additive]

section Additive
variable {R : Type r} [Ring R] (A : C) (ρ : R →+* End A)
  [(H.obj A).Additive]

/-- Original additive index maps remain additive after scalar enrichment. -/
instance coefficientModuleDiagram_additive : (H.coefficientModuleDiagram A ρ).Additive where
  map_add := by
    intro X Y f g
    apply (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective
    exact (H.obj A).map_add

end Additive

section Linear
variable {R : Type r} [CommRing R] [CategoryTheory.Linear R I]
  (A : C) (ρ : R →+* End A)

/-- Actual scalar identities, not noncentral module endomorphisms, give index-linearity. -/
theorem coefficientModuleDiagram_linear
    (hρ : ∀ (a : R) (i : I), (H.map (ρ a)).app i = (H.obj A).map (a • 𝟙 i)) :
    (H.coefficientModuleDiagram A ρ).Linear R := by
  rw [Functor.linear_iff]
  intro i a
  ext x
  change (H.obj A).map (a • 𝟙 i) x = (H.map (ρ a)).app i x
  exact (ConcreteCategory.congr_hom (hρ a i) x).symm

end Linear
end CategoryTheory.Functor
