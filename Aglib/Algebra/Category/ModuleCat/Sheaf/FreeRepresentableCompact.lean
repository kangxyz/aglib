/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentable
public import Mathlib.CategoryTheory.Presentable.Finite

/-! # Compactness of native free module sheaves

The original Hom-to-sections equivalence turns actual filtered section
continuity into finite presentation. Coefficients may be noncommutative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe c h r t k

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R] [HasSheafify J (ModuleCat.{max c h r t} R)]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Actual filtered section continuity makes the native free module sheaf
finitely presentable at the specified index size. -/
theorem isFinitelyPresentable_freeRepresentable (U : C)
    (hU : PreservesFilteredColimitsOfSize.{k, k}
      ((sheafSections J (ModuleCat.{max c h r t} R)).obj (Opposite.op U) ⋙
      forget (ModuleCat.{max c h r t} R))) :
    IsFinitelyPresentable.{k} ((freeRepresentableFunctor J R :
      C ⥤ Sheaf J (ModuleCat.{max c h r t} R)).obj U) := by
  let : ((sheafSections J (ModuleCat.{max c h r t} R)).obj (Opposite.op U) ⋙
      forget (ModuleCat.{max c h r t} R)).IsCardinalAccessible Cardinal.aleph0.{k} :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mpr hU
  exact Functor.isCardinalAccessible_of_natIso
    (freeRepresentableEvaluationIso J R U).symm Cardinal.aleph0.{k}

end ModuleCat.Sheaf
