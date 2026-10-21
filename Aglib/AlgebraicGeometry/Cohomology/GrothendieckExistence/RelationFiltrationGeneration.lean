/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationPositiveLifts
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationFiltration
public import Aglib.RingTheory.AdicCompletion.FilteredKernelGeneration

/-! # Actual homogeneous generation gives the original relation filtration step -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- Original positive homogeneous products of bounded lower-degree sections. -/
def relationPositiveSections (c j : ℕ) (U : X.Opens) :
    Set Γ(relationGradedPiece φ j, U) :=
  {z | ∃ r n, ∃ h : r + n = j, 0 < r ∧ n ≤ c ∧
    ∃ (a : ↥(I ^ r)) (y : Γ(relationGradedPiece φ n, U)),
      z = h ▸ (relationGradedScalarMap f I φ r n a).app U y}

/-- A genuine homogeneous spanning statement implies the original filtration
step. All lifts into the ideal multiple are constructed, not assumed. -/
theorem relationFiltration_le_ideal_sup_of_span (c j m : ℕ) (h : j + 1 ≤ m)
    [Epi (φ.hom.app (op m))] (U : X.affineOpens)
    (hspan : Submodule.span Γ(X, U.1) (relationPositiveSections f I φ c j U.1) = ⊤) :
    relationFiltration φ ((Nat.le_succ j).trans h) U.1 ≤
      (idealThickeningIdealSheaf f I).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(relation φ m, U.1)) ⊔
        relationFiltration φ h U.1 := by
  apply Submodule.le_sup_of_quotient_span_lifts
    (relationFiltration φ ((Nat.le_succ j).trans h) U.1)
    (relationFiltration φ h U.1)
    ((idealThickeningIdealSheaf f I).ideal U • ⊤)
    (relationFiltrationMap φ h U.1)
    (le_of_eq (ker_relationFiltrationMap φ h U.1))
    (relationPositiveSections f I φ c j U.1) hspan
  intro z hz
  obtain ⟨r, n, he, hr, _, a, y, rfl⟩ := hz
  subst j
  obtain ⟨x, hxI, hx0, hx⟩ := exists_positive_relation_section_lift f I φ r n m hr h a U y
  have hxmem : x ∈ relationFiltration φ ((Nat.le_succ (r + n)).trans h) U.1 := hx0
  refine ⟨⟨x, hxmem⟩, hxI, ?_⟩
  apply moduleHom_app_injective (kernel.ι (relationTransition φ (r + n))) U.1
  rw [relationFiltrationMap_ι]
  exact hx

end AlgebraicGeometry.Scheme.Cohomology
