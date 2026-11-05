/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Sites.SheafComposeColimits

/-! # Colimits of the original underlying module sheaf

Forgetting scalar structure preserves colimits on native module sheaves.
The ring universe remains independent of the site and value universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r

variable (R : Type r) [Ring R] {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)

/-- The original underlying abelian sheaf functor preserves colimits of the
site size. This is scalar forgetting, not a full embedding. -/
theorem underlying_preservesColimits :
    PreservesColimitsOfSize.{max u v, max u v} (underlying R J) := by
  let : HasSheafify J (ModuleCat.{max u v} R) := hasSheafify R J
  let : J.PreservesSheafification
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    forget_preservesSheafification R J
  let : PreservesColimitsOfSize.{max u v, max u v}
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v, r, max u v, max u v} R
  exact ⟨fun {_} {_} => sheafCompose_preservesColimitsOfShape J _⟩

end ModuleCat.Sheaf
