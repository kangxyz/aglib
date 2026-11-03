/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Congruence

/-!
# Coherence of original structural differential congruences

The original universal-derivation comparisons satisfy composition and inverse
laws. Equality induction uses their proved reflexivity; their constructors
are not replaced by equality-transport isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y : Scheme.{u}} {f g h : X ⟶ Y}

/-- Composition of the original structural differential comparisons. -/
theorem relativeDifferentialCongrIso_trans (hfg : f = g) (hgh : g = h) :
    relativeDifferentialCongrIso f hfg ≪≫ relativeDifferentialCongrIso g hgh =
      relativeDifferentialCongrIso f (hfg.trans hgh) := by
  cases hfg
  cases hgh
  simp only [relativeDifferentialCongrIso_refl, Iso.refl_trans]

/-- Reversing the structural equality reverses the same original comparison. -/
theorem relativeDifferentialCongrIso_symm (hfg : f = g) :
    (relativeDifferentialCongrIso f hfg).symm =
      relativeDifferentialCongrIso g hfg.symm := by
  cases hfg
  rw [relativeDifferentialCongrIso_refl]
  rfl

end AlgebraicGeometry.Scheme.Modules.Differentials
