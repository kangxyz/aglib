/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroSequence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Cohomological obstruction for the original square-zero unit sequence

The connecting map is Mathlib's original `Sheaf.H.δ`. Vanishing of the next
cohomology group of the actual additive kernel gives surjectivity for the
original map on unit cohomology. This is the cohomological input for Picard
lifting; no Picard classification or curve vanishing is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

universe u v w z
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, w}] [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{w})]
variable {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
variable [Presheaf.IsLocallySurjective J f.hom]

/-- The actual connecting homomorphism for the original square-zero unit sequence. -/
def squareZeroUnitsObstruction
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (q : ℕ) :
    H S.units q →+ H (additiveKernel f) (q + 1) :=
  H.δ (squareZeroUnitsComplex_shortExact f hf) q (q + 1) rfl

/-- A unit-cohomology class with zero actual obstruction lifts through the
original coefficient map. -/
theorem exists_unitsCohomology_lift_of_obstruction_eq_zero
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (q : ℕ)
    (x : H S.units q) (hx : squareZeroUnitsObstruction f hf q x = 0) :
    ∃ y : H R.units q, H.map (unitsMap f) q y = x :=
  H.longSequence_exact₃ (squareZeroUnitsComplex_shortExact f hf) x rfl hx

/-- Vanishing of the next kernel cohomology makes the original unit-cohomology
map surjective in every degree. -/
theorem unitsCohomology_map_surjective_of_subsingleton
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (q : ℕ)
    [Subsingleton (H (additiveKernel f) (q + 1))] :
    Function.Surjective (H.map (unitsMap f) q) := by
  intro x
  exact exists_unitsCohomology_lift_of_obstruction_eq_zero f hf q x (Subsingleton.elim _ _)

end CategoryTheory.Sheaf
