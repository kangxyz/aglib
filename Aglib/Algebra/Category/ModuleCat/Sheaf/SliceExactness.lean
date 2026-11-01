/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExactCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Exact native slice restriction for constant-ring module sheaves

The module coefficients supply the generic concrete sheafification hypotheses.
The scalar ring keeps its independent universe, and the value universe is the
standard site size. The functor and all its maps are the original over-pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c h r

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] (U : C)

attribute [local instance] hasSheafify

/-- Original module-valued slice restriction preserves epimorphisms. -/
instance overPullback_preservesEpimorphisms :
    (J.overPullback (ModuleCat.{max c h} Λ) U).PreservesEpimorphisms := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max c h} Λ)) :=
    forget_preservesFilteredColimits Λ
  let : J.PreservesSheafification (forget (ModuleCat.{max c h} Λ)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max c h} Λ))
  exact GrothendieckTopology.overPullback_preservesEpimorphisms J (ModuleCat.{max c h} Λ) U

/-- Original module-valued slice restriction preserves the actual homology objects and maps. -/
instance overPullback_preservesHomology :
    (J.overPullback (ModuleCat.{max c h} Λ) U).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Original module-valued slice restriction preserves finite colimits. -/
instance overPullback_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{max c h} Λ) U) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end ModuleCat.Sheaf
