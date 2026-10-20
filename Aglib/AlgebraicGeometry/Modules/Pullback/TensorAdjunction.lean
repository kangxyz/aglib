/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Pullback.TensorAdjunction` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fe073397bf23087d6c049e131088dea740876075523e6451b724eab0e45ae77b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_adjoint pushforwardTensorMap
    pushforwardTensorMap_naturality tensorSheafMap tensorSheafMap_comp)
namespace AlgebraicGeometry.Scheme.Modules.Pullback.Tensor
universe u

/-- The canonical tensor pullback comparison commutes with actual adjunction mates. -/
theorem tensor_adjoint {S T : Scheme.{u}} (f : S ⟶ T) (M N : T.Modules) (A B : S.Modules)
    (a : (Scheme.Modules.pullback f).obj M ⟶ A)
    (b : (Scheme.Modules.pullback f).obj N ⟶ B) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackTensorMap f M N ≫ tensorSheafMap S a b) =
      tensorSheafMap T ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ b) ≫
          pushforwardTensorMap f A B := by
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint]
  rw [Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc,
    tensorSheafMap_comp]
  rfl


end AlgebraicGeometry.Scheme.Modules.Pullback.Tensor
