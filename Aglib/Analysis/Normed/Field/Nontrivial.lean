/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Analysis.Normed.Field.Basic

/-!
# A small unit and a nontrivial norm

Source: `R5Lab.Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
namespace NormedField

universe u

/-- A small unit makes the existing norm nontrivial, using the native constructor. -/
@[instance_reducible] def nontrivialOfSmallUnit {F : Type u} [NormedField F] (q : Fˣ)
    (hq : ‖(q : F)‖ < 1) : NontriviallyNormedField F :=
  NontriviallyNormedField.ofNormNeOne ⟨(q : F), q.ne_zero, ne_of_lt hq⟩

end NormedField
