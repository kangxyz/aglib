/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.C1Cocycles
public import Aglib.FieldTheory.Tsen.AlgebraicFunctionField

/-!
# Actual finite-Galois cocycle primitives over algebraic function fields

This consumer combines finite-coefficient Tsen with the constructed crossed
product and its matrix splitting. It concludes the native multiplicative
coboundary equation, without asserting an unproved étale-cohomology comparison.
-/

@[expose] public section

namespace groupCohomology

variable (K E L : Type*) [Field K] [IsAlgClosed K] [Field E] [Field L]
variable [Algebra (RatFunc K) E] [Algebra.IsAlgebraic (RatFunc K) E]
variable [Algebra E L] [FiniteDimensional E L] [IsGalois E L]

include K

/-- A native multiplicative two-cocycle for any finite Galois extension of an
algebraic function field has an actual primitive, with no normalization premise. -/
theorem IsMulCocycle₂.isMulCoboundary₂_of_algebraic_ratFunc
    {c : (L ≃ₐ[E] L) × (L ≃ₐ[E] L) → Lˣ} (hc : IsMulCocycle₂ c) :
    IsMulCoboundary₂ c := by
  let : Infinite E := Infinite.of_injective
    (fun x : K => algebraMap (RatFunc K) E (algebraMap K (RatFunc K) x))
    ((algebraMap (RatFunc K) E).injective.comp (algebraMap K (RatFunc K)).injective)
  exact hc.isMulCoboundary₂_of_isC1 (Field.isC1_algebraic_ratFunc K E)

end groupCohomology
