/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationFiltrationGeneration

/-! # Bounded homogeneous generation controls the original relation reduction kernels -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- Finite descent gives the required original kernel bound at every level
above the generator-degree bound. The hypothesis is solely homogeneous span;
original transition lifts and their ideal membership have been proved. -/
theorem relation_kernel_le_ideal_of_homogeneous_span (c m : ℕ)
    [Epi (φ.hom.app (op m))] (U : X.affineOpens)
    (hspan : ∀ j, c < j → j < m →
      Submodule.span Γ(X, U.1) (relationPositiveSections f I φ c j U.1) = ⊤)
    (h : c + 1 ≤ m) :
    ((relationMap φ h).val.app (op U.1)).hom.ker ≤
      (idealThickeningIdealSheaf f I).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(relation φ m, U.1)) := by
  have hall : ∀ j (hj : j ≤ m), c < j → relationFiltration φ hj U.1 ≤
      (idealThickeningIdealSheaf f I).ideal U •
        (⊤ : Submodule Γ(X, U.1) Γ(relation φ m, U.1)) := by
    intro j hj
    induction hj using Nat.decreasingInduction with
    | self =>
      intro _
      simp only [relationFiltration, relationMap_refl]
      change (LinearMap.id : Γ(relation φ m, U.1) →ₗ[Γ(X, U.1)]
        Γ(relation φ m, U.1)).ker ≤ _
      rw [LinearMap.ker_id]
      exact bot_le
    | of_succ j hj ih =>
      intro hcj
      exact (relationFiltration_le_ideal_sup_of_span f I φ c j m
        (Nat.succ_le_of_lt hj) U (hspan j hcj hj)).trans
        (sup_le le_rfl (ih (by omega)))
  exact hall (c + 1) h (Nat.lt_succ_self c)

end AlgebraicGeometry.Scheme.Cohomology
