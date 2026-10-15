/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Additivity of native module-sheaf evaluation

The original variable-ring evaluation functor is additive. The instance
unfolds its existing forget/evaluation composition and preserves all ring,
module, site and morphism universes. It lets the native functor act on
complexes without introducing another section functor.
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

universe r m c h

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})

/-- Evaluation of actual module sheaves is additive, with the original component maps. -/
instance evaluation_additive (U : Cᵒᵖ) : (evaluation.{m} R U).Additive := by
  unfold evaluation
  infer_instance

end SheafOfModules
