/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.RatFuncCoefficientMap

/-! # Literal rational translation and coefficient extension -/

@[expose] public noncomputable section

namespace RatFunc

open Polynomial

variable {k L : Type*} [Field k] [Field L]

/-- The actual rational substitution induced by the native polynomial translation. -/
def translationHom (a : k) : RatFunc k →+* RatFunc k :=
  liftRingHom ((algebraMap k[X] (RatFunc k)).comp (algEquivAevalXAddC a).toRingHom)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((IsFractionRing.injective k[X] (RatFunc k)).comp (algEquivAevalXAddC a).injective))

@[simp]
theorem translationHom_polynomial (a : k) (q : k[X]) :
    translationHom a (algebraMap k[X] (RatFunc k) q) =
      algebraMap k[X] (RatFunc k) (algEquivAevalXAddC a q) :=
  liftRingHom_algebraMap _ _ q

@[simp]
theorem translationHom_C (a b : k) : translationHom a (C b) = C b := by
  simpa [algEquivAevalXAddC_apply] using translationHom_polynomial a (Polynomial.C b)

@[simp]
theorem translationHom_X (a : k) : translationHom a (X : RatFunc k) = X + C a := by
  simpa [algEquivAevalXAddC_apply] using translationHom_polynomial a Polynomial.X

end RatFunc

namespace Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

/-- Coefficient restriction commutes with literal rational translation. -/
theorem fractionMap_comp_translation (a : k) :
    (fractionMap φ).comp (RatFunc.translationHom a) =
      (RatFunc.translationHom (φ a)).comp (fractionMap φ) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, RatFunc.algebraMap_C, RatFunc.translationHom_C, fractionMap_C]
  · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, RatFunc.translationHom_X,
      fractionMap_X, map_add, fractionMap_C]

/-- The coefficient-translation square on each actual rational function. -/
theorem fractionMap_translation (a : k) (x : RatFunc k) :
    fractionMap φ (RatFunc.translationHom a x) =
      RatFunc.translationHom (φ a) (fractionMap φ x) :=
  RingHom.congr_fun (fractionMap_comp_translation φ a) x

end Polynomial.LocalResidue
