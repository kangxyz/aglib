/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleSections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentableCompact

/-! # Original fixed-ring free étale module generators are finitely presentable

At the existing geometric coefficient size, every qcqs original étale object
gives a compact native free module sheaf. The coefficient ring is unchanged
and may be noncommutative or have an infinite underlying additive group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

variable (R : Type (u + 1)) [Ring R] {X : Scheme.{u}}

attribute [local instance] ModuleCat.Sheaf.hasSheafify

/-- The genuine free module sheaf on an original qcqs étale object is
finitely presentable at the original geometric coefficient size. -/
theorem qcqs_freeModule_isFinitelyPresentable (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsFinitelyPresentable.{u + 1}
      ((ModuleCat.Sheaf.freeRepresentableFunctor.{u + 1, u + 1, u, 0} X.smallEtaleTopology R :
        X.Etale ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj U) := by
  apply ModuleCat.Sheaf.isFinitelyPresentable_freeRepresentable.{u + 1, u, u + 1, 0, u + 1}
  constructor
  intro I _ _
  let : PreservesColimitsOfShape I
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U)) :=
    Continuity.qcqsModuleSections_preservesFilteredColimits R U
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
