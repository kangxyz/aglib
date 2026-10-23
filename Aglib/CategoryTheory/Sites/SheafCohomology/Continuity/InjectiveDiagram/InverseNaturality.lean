/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseTransitions
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SystemCoherence

/-! # The original inverse-image square of a morphism of coefficient systems -/

@[expose] public noncomputable section
namespace CategoryTheory.InjectiveSystem
universe uI vI uA vA
variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)
  {F G : System D} (η : System.Hom D F G)

/-- Mate naturality follows from the given right-side system square. -/
lemma System.Hom.leftMap_naturality {i j : I} (a : i ⟶ j) :
    (D.left a).map (η.app i) ≫ G.leftMap D a =
      F.leftMap D a ≫ η.app j := by
  apply ((D.adj a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    System.homEquiv_leftMap, System.homEquiv_leftMap]
  exact η.naturality a

end CategoryTheory.InjectiveSystem
