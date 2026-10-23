/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOneBaseChange

/-!
# Original degree-one chart maps and native Spec squares

The native Proj chart is transported through a specified actual ring equivalence.
The original Spec-square paste retains all four displayed ring maps. These are
shared constructors for the scalar Rees chart and its graded augmentation consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

/-- The native degree-one chart transported through the specified actual ring equivalence. -/
def ringChartMap {R D T : Type u} [CommRing R] [CommRing D] [CommRing T]
    [Algebra R D] (G : ℕ → Submodule R D) [GradedAlgebra G]
    (f : D) (hf : f ∈ G 1) (E : T ≃+* Away G f) : Spec (.of T) ⟶ Proj G :=
  Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ Proj.awayι G f hf Nat.zero_lt_one

/-- Paste the original native Spec square with its displayed chart-map equation. -/
theorem spec_square_paste {A B C D : CommRingCat.{u}} {X Y : Scheme.{u}}
    (k : C ⟶ D) (m : B ⟶ C) (e : A ⟶ D) (n : B ⟶ A)
    (a : Spec C ⟶ X) (b : X ⟶ Y) (c : Spec B ⟶ Y)
    (hc : a ≫ b = Spec.map m ≫ c) (he : m ≫ k = n ≫ e) :
    (Spec.map k ≫ a) ≫ b = Spec.map e ≫ Spec.map n ≫ c := by
  rw [Category.assoc, hc, ← Spec.map_comp_assoc, he, Spec.map_comp_assoc]

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates
