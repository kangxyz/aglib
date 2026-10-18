/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.FreeDegree

/-!
# The coordinates generate the first twist of every module

For every module `F` on actual polynomial projective space with finitely many
coordinates, the coordinate multiplications `Xᵢ : O(0) ⊗ F → O(1 + 0) ⊗ F` jointly give
an epimorphism `∐ᵢ O(0) ⊗ F → O(1 + 0) ⊗ F`. Its cokernel is killed by every coordinate,
hence zero. This is the last map of the Koszul complex of the coordinates tensored with
`F`. It gives the syzygy sequence of the proof of Nitsure, arXiv:math/0504590v1,
Lemma 2.1 (b) (`Regularity/Monotone`); the Koszul complex itself (`Regularity/Koszul`) is
behind Lemma 2.1 (a) and (c). Twist multiplication with free target degrees,
`twistingTensorMultiplyTo`, lives in `ProjectiveSpace/Tensor/Monoidal/FreeDegree`, which this
leaf re-exports.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

/-- The sum of the coordinate multiplications `∐ᵢ O(0) ⊗ F → O(1 + 0) ⊗ F`. -/
def coordinateMultiplicationSum (F : (ProjectiveSpace R ι).Modules) :
    (∐ fun _ : ι =>
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι 0)).obj F) ⟶
      (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (((1 : ℕ) : ℤ) + 0))).obj F :=
  Sigma.desc fun i =>
    (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) 0 (coordinateSection R ι i)).app F

/-- The coordinate multiplications jointly generate `O(1 + 0) ⊗ F`. -/
instance epi_coordinateMultiplicationSum (F : (ProjectiveSpace R ι).Modules) :
    Epi (coordinateMultiplicationSum R ι F) := by
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_coordinate_eq_zero R ι
  intro i
  have hk : IsKilledByTwistSection R ι ((1 : ℕ) : ℤ) (coordinateSection R ι i)
      (cokernel (coordinateMultiplicationSum R ι F)) := by
    apply IsKilledByTwistSection.of_cokernel (cokernel.π (coordinateMultiplicationSum R ι F))
    have hι : (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) 0 (coordinateSection R ι i)).app F =
        Sigma.ι _ i ≫ coordinateMultiplicationSum R ι F := by
      unfold coordinateMultiplicationSum
      rw [Sigma.ι_comp_desc]
    rw [hι, Category.assoc, cokernel.condition, comp_zero]
  exact hk (-1)

end AlgebraicGeometry.ProjectiveSpace
