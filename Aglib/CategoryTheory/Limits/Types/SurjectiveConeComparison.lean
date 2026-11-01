/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Comparing original cones with surjective legs

Equivalences of the vertex and each stage which respect the original cone
legs automatically respect every transition when those legs are surjective.
They therefore transfer the limiting property without replacing either cone.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits.Types

universe v w u u'

variable {J : Type v} [Category.{w} J]
  {F : J ⥤ Type u} {G : J ⥤ Type u'}
  (cF : Cone F) (cG : Cone G)
  (e₀ : cF.pt ≃ cG.pt) (e : ∀ j, F.obj j ≃ G.obj j)
  (hleg : ∀ j x, e j (cF.π.app j x) = cG.π.app j (e₀ x))
  (hsurj : ∀ j, Function.Surjective (cF.π.app j))

include cF cG e₀ e hleg hsurj

/-- The whole transition law follows from the original surjective cone legs. -/
theorem naturality_of_surjective_cone_legs {i j : J} (f : i ⟶ j) (x : F.obj i) :
    e j (F.map f x) = G.map f (e i x) := by
  obtain ⟨y, rfl⟩ := hsurj i x
  have hF : F.map f (cF.π.app i y) = cF.π.app j y :=
    ConcreteCategory.congr_hom (cF.w f) y
  have hG : G.map f (cG.π.app i (e₀ y)) = cG.π.app j (e₀ y) :=
    ConcreteCategory.congr_hom (cG.w f) (e₀ y)
  rw [hF, hleg, hleg, hG]

/-- A limiting original target cone transfers along the vertex and stage equivalences. -/
theorem isLimit_of_surjective_cone_comparison (hG : IsLimit cG) :
    Nonempty (IsLimit cF) := by
  apply (isLimit_iff cF).mpr
  intro s hs
  let t : ∀ j, G.obj j := fun j => e j (s j)
  have ht : t ∈ G.sections := by
    intro i j f
    change G.map f (e i (s i)) = e j (s j)
    rw [← naturality_of_surjective_cone_legs cF cG e₀ e hleg hsurj f, hs f]
  obtain ⟨y, hy, huniq⟩ := (isLimit_iff cG).mp ⟨hG⟩ t ht
  refine ⟨e₀.symm y, ?_, ?_⟩
  · intro j
    apply (e j).injective
    rw [hleg, e₀.apply_symm_apply]
    exact hy j
  · intro x hx
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    apply huniq
    intro j
    change cG.π.app j (e₀ x) = e j (s j)
    rw [← hleg, hx]

end CategoryTheory.Limits.Types
