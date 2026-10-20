/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Length/PrimeQuotient.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`768fb677e4017d9c068d361b742be48479fe23dac39f4813762ce1a74537297c`.
-/

@[expose] public section

noncomputable section
open scoped _root_.TensorProduct
namespace Module
universe u

theorem primeQuotient_local_length {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] (A ⧸ p)) = 1 := by
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.AtPrime p) p).toLinearEquiv.length_eq]
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
  apply Module.length_eq_one_iff.mpr
  exact isSimpleModule_iff_quot_maximal.mpr
    ⟨IsLocalRing.maximalIdeal (Localization.AtPrime p), inferInstance,
      ⟨LinearEquiv.refl _ _⟩⟩

end Module
