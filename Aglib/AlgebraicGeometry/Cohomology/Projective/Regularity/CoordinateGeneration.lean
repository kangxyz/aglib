/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate

/-!
# The coordinates generate the first twist of every module

For every module `F` on actual polynomial projective space with finitely many
coordinates, the coordinate multiplications `Xᵢ : O(0) ⊗ F → O(1 + 0) ⊗ F` jointly give
an epimorphism `∐ᵢ O(0) ⊗ F → O(1 + 0) ⊗ F`. Its cokernel is killed by every coordinate,
hence zero. This is the last map of the Koszul complex of the coordinates tensored with
`F`, the first step of a Koszul route to the regularity statements of Nitsure,
arXiv:math/0504590v1, Lemma 2.1, and Stacks, Tag 08A6. Both sources prove them by
hyperplane sections over an infinite field; the Koszul route planned here is a different
proof of the same statements.
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

omit [Finite ι] in
variable {ι} in
/-- Multiplication by a global section `s` of `O(a)` from the twist `d` to a twist `d'` with
`a + d = d'`. The free target degree avoids transports between Koszul terms. -/
def twistingTensorMultiplyTo (a d d' : ℤ) (h : a + d = d')
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤)) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d) ⟶
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d') :=
  moduleTensorCoefficientMap (ProjectiveSpace R ι)
    (twistingMultiplyGlobal R ι a d s ≫ eqToHom (congrArg (twistingSheaf R ι) h))

omit [Finite ι] in
variable {ι} in
/-- With the canonical target degree it is `twistingTensorMultiply`. -/
theorem twistingTensorMultiplyTo_rfl (a d : ℤ)
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤)) :
    twistingTensorMultiplyTo R a d (a + d) rfl s = twistingTensorMultiply R ι a d s := by
  simp only [twistingTensorMultiplyTo, eqToHom_refl, Category.comp_id]
  rfl

omit [Finite ι] in
variable {ι} in
-- Section types of twists agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplications by two global twist sections commute, for arbitrary intermediate twists. -/
theorem twistingTensorMultiplyTo_comm (a b d d₁ d₂ e₁ : ℤ) (h₁ : a + d = d₁)
    (h₂ : b + d₁ = d₂) (h₃ : b + d = e₁) (h₄ : a + e₁ = d₂)
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤))
    (t : (twistingSheaf R ι b).val.obj (Opposite.op ⊤)) :
    twistingTensorMultiplyTo R a d d₁ h₁ s ≫ twistingTensorMultiplyTo R b d₁ d₂ h₂ t =
      twistingTensorMultiplyTo R b d e₁ h₃ t ≫ twistingTensorMultiplyTo R a e₁ d₂ h₄ s := by
  subst h₁ h₂ h₃
  simp only [twistingTensorMultiplyTo, eqToHom_refl, Category.comp_id,
    ← moduleTensorCoefficientMap_comp]
  congr 1
  ext V x
  apply Subtype.ext
  funext i
  change ((twistingMultiplyGlobal R ι b (a + d) t).val.app (Opposite.op V)
      ((twistingMultiplyGlobal R ι a d s).val.app (Opposite.op V) x)).val i =
    ((eqToHom (congrArg (twistingSheaf R ι) h₄)).val.app (Opposite.op V)
      ((twistingMultiplyGlobal R ι a (b + d) s).val.app (Opposite.op V)
        ((twistingMultiplyGlobal R ι b d t).val.app (Opposite.op V) x))).val i
  rw [twistingSection_eqToHom_val R ι h₄]
  simp only [twistingMultiplyGlobal_app, twistingSectionMul_apply]
  ring

end AlgebraicGeometry.ProjectiveSpace
