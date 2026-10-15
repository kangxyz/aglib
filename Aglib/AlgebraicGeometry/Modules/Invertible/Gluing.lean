/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic

/-!
# Rank-one module sheaves from actual transition cocycles

For a covering family of scheme opens, an actual unit cocycle glues to an actual line bundle.
The local singleton bases use the original cover and the canonical component-projection
trivializations. The same bases give finite local freeness and finite presentation, over every
scheme and without a Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (c : UnitCocycle U)

/-- Integer powers of the actual transition units define a new rank-one cocycle. -/
def zpow (n : ℤ) : UnitCocycle U where
  transition i j := c.transition i j ^ n
  cocycle i j k V hi hj hk := by
    simp only [map_zpow, ← mul_zpow]
    exact congrArg (fun t => t ^ n) (c.cocycle i j k V hi hj hk)

@[simp]
theorem zpow_transition (n : ℤ) (i j : ι) :
    (c.zpow n).transition i j = c.transition i j ^ n := rfl

@[simp]
theorem zpow_transitionOn (n : ℤ) (i j : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    (c.zpow n).transitionOn i j hi hj = c.transitionOn i j hi hj ^ n := by
  simp [transitionOn]

/-- The singleton free-module trivialization associated to a chart of the cocycle. -/
def localFreeIso (i : ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (U i)) PUnit.{u + 1} ≅ c.sheaf.over (U i) :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} =>
    SheafOfModules.unit (X.ringCatSheaf.over (U i))) ≪≫ (c.localIso i).symm

/-- The local singleton bases retain the supplied covering family. -/
def localGeneratorsData (hU : iSup U = ⊤) : SheafOfModules.LocalGeneratorsData.{u} c.sheaf where
  I := ι
  X := U
  coversTop := by
    intro V x hxV
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    exact ⟨U i ⊓ V, homOfLE inf_le_right, ⟨i, ⟨homOfLE inf_le_left⟩⟩, hi, hxV⟩
  generators i :=
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U i)) PUnit.{u + 1}).ofEpi (c.localFreeIso i).hom

instance localGeneratorsData_isLocallyFreeData (hU : iSup U = ⊤) :
    (c.localGeneratorsData hU).IsLocallyFreeData where
  isIso i := by
    change ι at i
    exact inferInstanceAs (IsIso
      ((SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U i)) PUnit.{u + 1}).ofEpi (c.localFreeIso i).hom).π)

instance localGeneratorsData_isFiniteType (hU : iSup U = ⊤) :
    (c.localGeneratorsData hU).IsFiniteType where
  isFiniteType i := by
    constructor
    change Finite PUnit.{u + 1}
    infer_instance

/-- The glued actual module sheaf is locally rank one on the original cover. -/
theorem isLocallyRankOne (hU : iSup U = ⊤) : IsLocallyRankOne X c.sheaf :=
  ⟨c.localGeneratorsData hU, inferInstance, fun _ => ⟨Equiv.refl _⟩⟩

/-- The glued actual module sheaf is finite locally free, witnessed by the same singleton bases. -/
theorem isFiniteLocallyFree (hU : iSup U = ⊤) : IsFiniteLocallyFree X c.sheaf :=
  ⟨c.localGeneratorsData hU, inferInstance, inferInstance⟩

/-- The actual line bundle glued from the supplied unit cocycle. -/
def lineBundle (hU : iSup U = ⊤) : LineBundle X :=
  ⟨c.sheaf, c.isLocallyRankOne hU⟩

/-- Noetherianity is unnecessary for finite presentation of a glued line bundle. -/
theorem isFinitePresentation (hU : iSup U = ⊤) : c.sheaf.IsFinitePresentation := by
  let := c.isFiniteLocallyFree hU
  infer_instance

/-- The glued line bundle is quasicoherent over every scheme. -/
theorem isQuasicoherent (hU : iSup U = ⊤) : c.sheaf.IsQuasicoherent := by
  let := c.isFiniteLocallyFree hU
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
