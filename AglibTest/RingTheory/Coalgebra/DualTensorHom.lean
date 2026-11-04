/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualTensorHom

/-! Native tensor–Hom and coevaluation consumers. -/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct Module.Dual.FiniteDual

example {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]
    [Ring B] [Algebra R B] [Module.Finite R A] [Module.Projective R A] :
    (TensorProduct.dualTensorHomAlgEquiv R A B).toLinearEquiv =
      dualTensorHomEquiv R A B ≪≫ₗ (WithConv.linearEquiv R (A →ₗ[R] B)).symm :=
  TensorProduct.dualTensorHomAlgEquiv_toLinearEquiv R A B

example {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    dualTensorHom k V V
        (TensorProduct.comm k V (Dual k V) (coevaluation k V 1)) = LinearMap.id :=
  TensorProduct.dualTensorHom_coevaluation k V
