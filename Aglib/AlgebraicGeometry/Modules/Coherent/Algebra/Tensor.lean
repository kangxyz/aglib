/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite-type closure of the original module-sheaf tensor

The affine-locally finite-type predicate is closed under the actual ambient tensor.
This does not put another monoidal structure on coherent sheaves. No Noetherianity
is needed for finite-type quasicoherent closure; on a locally Noetherian scheme it
is the coherent tensor closure.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The actual tensor of two affine finite-type quasicoherent sheaves is finite type. -/
theorem affineFiniteSheaf_tensor (R : CommRingCat.{u}) (M N : (Spec R).Modules)
    (hM : affineFiniteSheaf R M) (hN : affineFiniteSheaf R N) :
    affineFiniteSheaf R (M ⊗ N) := by
  let hMQc : M.IsQuasicoherent := hM.1
  let hNQc : N.IsQuasicoherent := hN.1
  let hMFinite : Module.Finite R (moduleSpecΓFunctor.obj M) := hM.2
  let hNFinite : Module.Finite R (moduleSpecΓFunctor.obj N) := hN.2
  let P := moduleSpecΓFunctor.obj M ⊗ moduleSpecΓFunctor.obj N
  let hPFinite : Module.Finite R P :=
    inferInstanceAs (Module.Finite R (TensorProduct R
      (moduleSpecΓFunctor.obj M) (moduleSpecΓFunctor.obj N)))
  let e : M ⊗ N ≅ tilde P :=
    tensorSheafIso (Spec R) (asIso M.fromTildeΓ).symm
      (asIso N.fromTildeΓ).symm ≪≫
      tildeTensorIso (moduleSpecΓFunctor.obj M) (moduleSpecΓFunctor.obj N)
  have hP : affineFiniteSheaf R (tilde P) :=
    ⟨inferInstance, Module.Finite.equiv (tilde.isoTop P).toLinearEquiv⟩
  exact (affineFiniteSheaf R).prop_of_iso e.symm hP

/-- Finite-type quasicoherent sheaves are closed under the original ambient tensor. -/
theorem affineLocallyFiniteType_tensor {X : Scheme.{u}} (M N : X.Modules)
    (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N) :
    affineLocallyFiniteType X (M ⊗ N) := by
  intro R j hj
  exact (affineFiniteSheaf R).prop_of_iso (tensorRestrictionIso j M N)
    (affineFiniteSheaf_tensor R (M.restrict j) (N.restrict j) (hM R j) (hN R j))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
