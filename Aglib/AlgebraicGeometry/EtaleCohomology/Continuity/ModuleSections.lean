/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingColimits

/-! # Fixed-ring module sections on original qcqs étale objects

Filtered colimits of original module sections are detected after forgetting
scalar structure. No finiteness of the underlying additive groups, change of
the coefficient ring, or commutativity of scalars is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u r

variable (R : Type r) [Ring R] {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

attribute [local instance] ModuleCat.Sheaf.hasSheafify

/-- Original sections of native module sheaves on a qcqs object preserve
filtered coefficient colimits, for the same arbitrary coefficient ring. -/
theorem qcqsModuleSections_preservesFilteredColimits (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    PreservesColimitsOfShape I
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U)) := by
  let : PreservesColimitsOfSize.{u + 1, u + 1}
      (ModuleCat.Sheaf.underlying R X.smallEtaleTopology) :=
    ModuleCat.Sheaf.underlying_preservesColimits R X.smallEtaleTopology
  let : PreservesColimitsOfShape I
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) :=
    qcqsSectionsPreservesFilteredColimits (I := I) U
  let : PreservesColimitsOfShape I
      (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U)) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesColimitsOfShape I
      (ModuleCat.Sheaf.underlying R X.smallEtaleTopology ⋙
        (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)))
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
