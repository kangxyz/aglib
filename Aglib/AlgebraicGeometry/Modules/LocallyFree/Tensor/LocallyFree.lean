/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Finite local freeness of the original tensor

The original affine section modules are finite projective, hence so is their
tensor. The native tilde comparison and actual open restriction transfer their
finite local bases to the unchanged sheaf tensor. No Noetherian or flat-base
hypothesis is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The original tensor of affine vector bundles is finite locally free. -/
theorem finiteLocallyFree_tensor_affine (R : CommRingCat.{u})
    (M N : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] [IsFiniteLocallyFree (Spec R) N] :
    IsFiniteLocallyFree (Spec R) (M ⊗ N) := by
  let : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  let : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let P := moduleSpecΓFunctor.obj M
  let Q := moduleSpecΓFunctor.obj N
  let : Module.Finite R P := finite_globalSections_of_finiteLocallyFree R M
  let : Module.Finite R Q := finite_globalSections_of_finiteLocallyFree R N
  let : Module.Projective R P := projective_globalSections_of_finiteLocallyFree R M
  let : Module.Projective R Q := projective_globalSections_of_finiteLocallyFree R N
  let T : ModuleCat R := ModuleCat.of R (TensorProduct R P Q)
  let : Module.Finite R T :=
    inferInstanceAs (Module.Finite R (TensorProduct R P Q))
  let : Module.Projective R T :=
    inferInstanceAs (Module.Projective R (TensorProduct R P Q))
  let : IsFiniteLocallyFree (Spec R) (tilde T) :=
    finiteLocallyFree_tilde_of_finite_projective R T
  let e : tilde T ≅ M ⊗ N :=
    (tildeTensorIso P Q).symm ≪≫
      tensorSheafIso (Spec R) (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
  exact finiteLocallyFree_of_iso e

/-- Tensor products of finite locally free sheaves are finite locally free on any scheme. -/
theorem finiteLocallyFree_tensor {X : Scheme.{u}} (M N : X.Modules)
    [IsFiniteLocallyFree X M] [IsFiniteLocallyFree X N] :
    IsFiniteLocallyFree X (M ⊗ N) := by
  let 𝒰 := X.affineOpenCover
  apply finiteLocallyFree_of_affineCharts (M ⊗ N) 𝒰.X 𝒰.f
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)
  intro i
  let : IsFiniteLocallyFree (Spec (𝒰.X i)) ((M.restrict (𝒰.f i)) ⊗
      (N.restrict (𝒰.f i))) :=
    finiteLocallyFree_tensor_affine (𝒰.X i) (M.restrict (𝒰.f i)) (N.restrict (𝒰.f i))
  let e : (M.restrict (𝒰.f i)) ⊗ (N.restrict (𝒰.f i)) ≅
      (M ⊗ N).restrict (𝒰.f i) := tensorRestrictionIso (𝒰.f i) M N
  exact finiteLocallyFree_of_iso e

end AlgebraicGeometry.Scheme.Modules
