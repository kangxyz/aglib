/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.HyperplaneStep
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Hyperplane
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Bound
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Ambient
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.FieldExtension
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.HyperplaneSections

/-! Focused consumer of Mumford's hyperplane step, of hyperplane sections kept on projective
space, of Mumford's bound conditional on hyperplane sections, and of its descent along a field
extension; also guards the general lemmas this slice moved into their owners (connecting maps,
dimension comparisons, frame coefficients, Remark 2.2, homogeneous dimension count). -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

/-- Mumford's step: `F` is `m₀ + h⁰(F(m₀ - 1)) - χ(F(m₀ - 1))`-regular. -/
example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace k ι).Modules) (hS : S.ShortExact)
    (φ : S.X₁ ≅ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (-1))).obj S.X₂)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₂)
    (h₃ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₃) (m₀ : ℤ)
    (hreg : IsProjectiveRegular k ι S.X₃ m₀) :
    IsProjectiveRegular k ι S.X₂ (m₀ + projectiveCohomologyDim k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι (m₀ - 1))).obj S.X₂)
        0 - projectiveHilbertFunction k ι S.X₂ (m₀ - 1)) :=
  IsProjectiveRegular.of_hyperplane_euler S φ n e hS h₂ h₃ hreg

/-- Mumford's bound for subsheaves of `O^p` over a field with hyperplane sections. -/
example (k : Type u) [Field k] (ι : Type u) (n p : ℕ) (e : ι ≃ Fin (n + 1))
    (hgen : HasHyperplaneSections k ι) (F : (ProjectiveSpace k ι).Modules)
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections n p e hgen j hF a hχ

/-- The descent: an extension with hyperplane sections. -/
example (k K : Type u) [Field k] [Field K] [Algebra k K] (ι : Type u) (n p : ℕ)
    (e : ι ≃ Fin (n + 1)) (hgen : HasHyperplaneSections K ι) (F : (ProjectiveSpace k ι).Modules)
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  isProjectiveRegular_mumfordBound_free_of_extension n p e hgen j hF a hχ

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane_restrict'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane_restrict

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane_euler'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_hyperplane_euler

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_zero_le_of_shortExact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_zero_le_of_shortExact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_one_le_of_shortExact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_one_le_of_shortExact

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.mono_hyperplaneCokernelMap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.mono_hyperplaneCokernelMap

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_hyperplane'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertFunction_hyperplane

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isZero_of_projectiveHilbertFunction_eq_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isZero_of_projectiveHilbertFunction_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_of_hasHyperplaneSections'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProjectiveRegular_mumfordBound_of_hasHyperplaneSections

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isMumfordAmbient_twistingCoproduct'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isMumfordAmbient_twistingCoproduct

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_ideal_of_hasHyperplaneSections'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProjectiveRegular_mumfordBound_ideal_of_hasHyperplaneSections

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.HasHyperplaneSections.of_up'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.HasHyperplaneSections.of_up

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSectionsUp_of_isSMulRegular'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.hasHyperplaneSectionsUp_of_isSMulRegular

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_pullback_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_pullback_map

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_free_of_extension'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.isProjectiveRegular_mumfordBound_free_of_extension

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyConnectingOfHom_zero_eq_zero_of_surjective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleCohomologyConnectingOfHom_zero_eq_zero_of_surjective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomologyConnectingOfHom_eq_zero_iff_injective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleCohomologyConnectingOfHom_eq_zero_iff_injective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.TwistSectionsOnto.succ'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.TwistSectionsOnto.succ

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_eq_zero_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_eq_zero_iff

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_le_of_surjective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_le_of_surjective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_le_of_injective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_le_of_injective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_eq_iff_injective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_eq_iff_injective

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_zero_le_of_mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveCohomologyDim_zero_le_of_mono

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.unitHom_eq_zero_of_subsingleton'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.unitHom_eq_zero_of_subsingleton

/--
info: 'AlgebraicGeometry.ProjectiveSpace.frameCoefficient_smul_eq_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.frameCoefficient_smul_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.mono_twistingTensorMultiply_of_isSMulRegular'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.mono_twistingTensorMultiply_of_isSMulRegular

/--
info: 'MvPolynomial.finrank_homogeneousSubmodule_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.finrank_homogeneousSubmodule_le
