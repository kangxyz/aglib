/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Quotient.Unit
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk

/-! # Epimorphy of the original closed-immersion quotient unit -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The original unit for a closed immersion is an epimorphism on every
module sheaf, with no quasicoherence or finiteness assumption. -/
instance pullbackPushforwardUnit_epi {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (M : Y.Modules) :
    Epi ((pullbackPushforwardAdjunction f).unit.app M) := by
  apply epi_of_moduleStalk
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    have h : Epi ((moduleStalk Y (f x)).map
        ((pullbackPushforwardAdjunction f).unit.app M) ≫
          (pushforwardModuleStalkIso f f.isClosedEmbedding.isInducing x).hom.app
            ((pullback f).obj M) ≫
          (ModuleCat.restrictScalars (f.stalkMap x).hom).map
            ((pullbackModuleStalkIso f x).hom.app M)) := by
      rw [pullbackPushforwardUnit_moduleStalk f f.isClosedEmbedding.isInducing x M]
      exact ModuleCat.extendRestrictScalarsAdj_unit_epi
        (f.stalkMap x).hom (f.stalkMap_surjective x) ((moduleStalk Y (f x)).obj M)
    simpa only [epi_comp_iff_of_isIso] using h
  · exact (isZero_closedImmersion_moduleStalk_of_not_mem f y hy
      ((pullback f).obj M)).epi _

end AlgebraicGeometry.Scheme.Modules
