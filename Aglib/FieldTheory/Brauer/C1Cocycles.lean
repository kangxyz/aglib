/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.C1Primitive
public import Aglib.FieldTheory.Brauer.CrossedProduct.Normalization

/-!
# Native finite-Galois two-cocycle primitives over infinite C₁ fields

No normalization or crossed-product existence is assumed. Normalization,
the actual central simple crossed product, C₁ splitting, and the coefficients
of a one-dimensional extension-field action construct the primitive.
This is not yet an identification with original étale cohomology.
-/

@[expose] public section

namespace groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Every native multiplicative finite-Galois two-cocycle over an infinite C₁
field has an actual native multiplicative primitive. -/
theorem IsMulCocycle₂.isMulCoboundary₂_of_isC1
    [Infinite K] [FiniteDimensional K L] [IsGalois K L]
    {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hc : IsMulCocycle₂ c) (hK : Field.IsC1 K) : IsMulCoboundary₂ c :=
  isMulCoboundary₂_of_normalize
    (CrossedProduct.isMulCoboundary₂_of_isC1 hK hc.normalize (normalize₂_one_one c))

end groupCohomology
