/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext

/-!
# Degree-zero section normalization for module Ext

The canonical comparison from structure-module Ext to additive cohomology
agrees with evaluation of the original module morphism on the global section
one. Both section comparisons are the existing native maps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u})

/-- The canonical comparison sends an original module morphism to its section at one. -/
theorem moduleExtCohomologyMap_mk₀_sections (M : X.Modules)
    (f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
        (moduleExtCohomologyMap X M 0 (Ext.mk₀ f)) =
      Scheme.Modules.unitHomGlobalSectionsEquiv X M f := by
  change integerSheafHomEquiv (moduleAddSheaf X M)
      (Ext.addEquiv₀ (moduleExtCohomologyMap X M 0 (Ext.mk₀ f))) = _
  rw [moduleExtCohomologyMap_mk₀, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, ← moduleUnitIntegerHomEquiv_apply]
  exact AddEquiv.apply_symm_apply _ _

/-- Native H⁰ of the canonical Ext comparison is the original unit-module section map. -/
theorem moduleExtCohomologyMap_sections (M : X.Modules)
    (x : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules) M 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
        (moduleExtCohomologyMap X M 0 x) =
      Scheme.Modules.unitHomGlobalSectionsEquiv X M (Ext.addEquiv₀ x) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (SheafOfModules.unit X.ringCatSheaf) M).surjective x
  rw [moduleExtCohomologyMap_mk₀_sections, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Cohomology
