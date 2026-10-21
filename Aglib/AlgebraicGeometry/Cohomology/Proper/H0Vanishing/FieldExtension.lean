/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension
public import Aglib.AlgebraicGeometry.Cohomology.Proper.H0Vanishing

/-!
# A vanishing neighbourhood from an extended actual fibre

Vanishing on an arbitrary field extension of an actual residue-field fibre
reflects to that same original fibre. Existing proper semicontinuity then
constructs an open neighbourhood with vanishing on every actual fibre.
The generic-point application needs no new openness assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Vanishing on a field extension of the literal point fibre is equivalent
to vanishing of its original cohomology, in every degree. -/
theorem subsingleton_modulePointFiberCohomology_iff_fieldBaseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (y : Y)
    {K : Type u} [Field K] (σ : Y.residueField y →+* K) :
    Subsingleton (modulePointFiberCohomology f M n y) ↔
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf _ ((Scheme.Modules.pullback
          (pullback.fst (f.fiberToSpecResidueField y)
            (Spec.map (CommRingCat.ofHom σ)))).obj
          ((Scheme.Modules.pullback (f.fiberι y)).obj M))) n) := by
  let : QuasiSeparated (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact subsingleton_moduleCohomology_iff_fieldBaseChange
    (f.fiberToSpecResidueField y) σ ((Scheme.Modules.pullback (f.fiberι y)).obj M) n

/-- For a proper finite-type quasicoherent relatively flat coefficient,
vanishing on any field extension of an actual fibre supplies a vanishing
neighbourhood of that original point. -/
theorem exists_open_subsingleton_modulePointFiberH0_of_fieldBaseChange
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (y : Y) {K : Type u} [Field K] (σ : Y.residueField y →+* K)
    (hzero : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf _ ((Scheme.Modules.pullback
        (pullback.fst (f.fiberToSpecResidueField y)
          (Spec.map (CommRingCat.ofHom σ)))).obj
        ((Scheme.Modules.pullback (f.fiberι y)).obj M))) 0)) :
    ∃ U : Y.Opens, y ∈ U ∧
      ∀ z : Y, z ∈ U → Subsingleton (modulePointFiberCohomology f M 0 z) := by
  let U : Y.Opens := ⟨{z : Y | Subsingleton (modulePointFiberCohomology f M 0 z)},
    isOpen_setOf_subsingleton_modulePointFiberH0_of_proper f M hM hflat⟩
  refine ⟨U, ?_, fun z hz => hz⟩
  exact (subsingleton_modulePointFiberCohomology_iff_fieldBaseChange f M 0 y σ).mpr hzero

end AlgebraicGeometry.Scheme.Cohomology
