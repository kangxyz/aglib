/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Global
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Multiplication

/-!
# Prescribed negative degrees for actual section extensions

Multiplication by the selected coordinate power raises the negative degree of a twist
source. On the selected chart its original standard coefficient is one. Composing with
an already constructed section extension therefore retains the original generator image
in every larger negative degree, without another denominator-clearing or gluing argument.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original coordinate-power multiplication from a more negative twist to a chosen
negative twist, with only the canonical equality transport of its target degree. -/
def negativeTwistCoordinatePowerMap (i : ι) (N₀ N : ℕ) (hN : N₀ ≤ N) :
    twistingSheaf R ι (-(N : ℤ)) ⟶ twistingSheaf R ι (-(N₀ : ℤ)) :=
  polynomialMultiplication R ι (N - N₀) (coordinatePower R ι (N - N₀) i) (-(N : ℤ)) ≫
    eqToHom (congrArg (twistingSheaf R ι)
      (show ((N - N₀ : ℕ) : ℤ) + -(N : ℤ) = -(N₀ : ℤ) by omega))

/-- The selected coordinate power sends the original selected-chart generator to the
original generator of the target twist, with coefficient exactly one. -/
theorem negativeTwistCoordinatePowerMap_generator (i : ι) (N₀ N : ℕ) (hN : N₀ ≤ N) :
    (negativeTwistCoordinatePowerMap R ι i N₀ N hN).val.app (op (coordinateOpen R ι i))
        ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1) =
      (twistingSectionsEquiv R ι (-(N₀ : ℤ)) i le_rfl).symm 1 := by
  have htransport (a b : ℤ) (h : a = b)
      (s : Γ(twistingSheaf R ι a, coordinateOpen R ι i)) :
      twistingSectionsEquiv R ι b i le_rfl
          ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app
            (op (coordinateOpen R ι i)) s) = twistingSectionsEquiv R ι a i le_rfl s := by
    subst b
    rfl
  have hdeg : ((N - N₀ : ℕ) : ℤ) + -(N : ℤ) = -(N₀ : ℤ) := by omega
  apply (twistingSectionsEquiv R ι (-(N₀ : ℤ)) i le_rfl).injective
  rw [LinearEquiv.apply_symm_apply]
  change twistingSectionsEquiv R ι (-(N₀ : ℤ)) i le_rfl
      ((eqToHom (congrArg (twistingSheaf R ι) hdeg)).val.app
        (op (coordinateOpen R ι i))
        ((polynomialMultiplication R ι (N - N₀)
          (coordinatePower R ι (N - N₀) i) (-(N : ℤ))).val.app
            (op (coordinateOpen R ι i))
            ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1))) = 1
  rw [htransport _ _ hdeg, polynomialMultiplication_local, LinearEquiv.apply_symm_apply, mul_one]
  simp only [homogeneousChartSection, homogeneousChartFraction_coordinatePower]
  exact (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)).hom.map_one

variable (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent] [Finite ι]

/-- Every original chart section extends from all sufficiently negative twists, with the
same original selected-chart generator image in every degree. -/
theorem exists_negativeTwistHom_generator_eventually (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M,
        φ.val.app (op (coordinateOpen R ι i))
          ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1) = s := by
  obtain ⟨N₀, φ₀, hφ₀⟩ := exists_negativeTwistHom_generator R ι M i s
  refine ⟨N₀, ?_⟩
  intro N hN
  refine ⟨negativeTwistCoordinatePowerMap R ι i N₀ N hN ≫ φ₀, ?_⟩
  change φ₀.val.app (op (coordinateOpen R ι i))
    ((negativeTwistCoordinatePowerMap R ι i N₀ N hN).val.app (op (coordinateOpen R ι i))
      ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1)) = s
  rw [negativeTwistCoordinatePowerMap_generator]
  exact hφ₀

/-- A section extension can be chosen beyond any prescribed negative-degree bound. -/
theorem exists_negativeTwistHom_generator_ge (B : ℕ) (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ N : ℕ, B ≤ N ∧ ∃ φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M,
      φ.val.app (op (coordinateOpen R ι i))
        ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1) = s := by
  obtain ⟨N₀, hN₀⟩ := exists_negativeTwistHom_generator_eventually R ι M i s
  exact ⟨max B N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

end AlgebraicGeometry.ProjectiveSpace
