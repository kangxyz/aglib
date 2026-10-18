/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.TensorCharpolyProduct
public import Lean.Util.CollectAxioms

/-! Regression tests for the literal tensor decomposition characteristic polynomial. -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AglibTest.TensorCharpolyProduct

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra F L] [FiniteDimensional F E]
  {ι : Type*} [Fintype ι] (D : ι → Type*) [∀ i, Field (D i)]
  [∀ i, Algebra L (D i)] [∀ i, FiniteDimensional L (D i)]

/-- The product uses the actual tensor images, without assumed factor identities. -/
theorem literalTensorImages (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : E) :
    ((Algebra.lmul F E b).charpoly).map (algebraMap F L) =
      ∏ i, (Algebra.lmul L (D i) ((ε (1 ⊗ₜ[F] b)) i)).charpoly :=
  Algebra.map_charpoly_lmul_eq_prod_tensor D ε b

/-- The dependent finite-product formula is itself proved, not an input. -/
theorem actualProduct (a : ∀ i, D i) :
    (Algebra.lmul L (∀ i, D i) a).charpoly =
      ∏ i, (Algebra.lmul L (D i) (a i)).charpoly :=
  Algebra.charpoly_lmul_pi D a

open Lean in
run_cmd do
  for name in #[``Algebra.charpoly_lmul_algEquiv, ``Algebra.charpoly_lmul_prod,
      ``Algebra.charpoly_lmul_pi, ``Algebra.map_charpoly_lmul_eq_prod_tensor,
      ``literalTensorImages, ``actualProduct] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal tensor characteristic-polynomial products use only standard foundations."

end AglibTest.TensorCharpolyProduct
