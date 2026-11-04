/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.HopfAlgebra.FiniteDualEvaluation

/-! The canonical evaluation unit retains the native coevaluation and antipode. -/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct Module.Dual.FiniteDual

variable {k A : Type*} [Field k] [Ring A] [HopfAlgebra k A] [FiniteDimensional k A]

example : (HopfAlgebra.coevaluationUnit k A).val = coevaluation k A 1 := rfl

example : IsUnit (coevaluation k A 1) := (HopfAlgebra.coevaluationUnit k A).isUnit

example : HopfAlgebra.evaluationEndEquiv k A (coevaluation k A 1) = toConv LinearMap.id :=
  HopfAlgebra.evaluationEndEquiv_coevaluation k A

example : (HopfAlgebra.coevaluationUnit k A)⁻¹.val =
    (HopfAlgebra.antipode k (A := A)).rTensor (Dual k A) (coevaluation k A 1) := rfl
