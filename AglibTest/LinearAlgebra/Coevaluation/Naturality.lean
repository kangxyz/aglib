/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.LinearAlgebra.Coevaluation.Naturality

/-! Naturality retains the original native coevaluation and transpose on whole linear maps. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]

example (f : V →ₗ[k] W) :
    TensorProduct.map f (LinearMap.id : Dual k V →ₗ[k] Dual k V) ∘ₗ coevaluation k V =
      TensorProduct.map (LinearMap.id : W →ₗ[k] W) f.dualMap ∘ₗ coevaluation k W :=
  TensorProduct.coevaluation_naturality f

example (f : V →ₗ[k] W) (r : k) :
    TensorProduct.map f (LinearMap.id : Dual k V →ₗ[k] Dual k V) (coevaluation k V r) =
      TensorProduct.map (LinearMap.id : W →ₗ[k] W) f.dualMap (coevaluation k W r) :=
  TensorProduct.coevaluation_naturality_apply f r

variable (K : Type*) [Field K] [Algebra k K]

example :
    TensorProduct.coevaluationBaseChangeMap k V K (coevaluation k V 1) =
      coevaluation K (K ⊗[k] V) 1 :=
  TensorProduct.coevaluation_baseChange_one k V K

example :
    TensorProduct.coevaluationBaseChangeMap k V K ∘ₗ coevaluation k V =
      (coevaluation K (K ⊗[k] V)).restrictScalars k ∘ₗ Algebra.linearMap k K :=
  TensorProduct.coevaluation_baseChange k V K
