/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# The structure-module quotient of a closed immersion

The actual structure-module map of a closed immersion is an epimorphism.
Together with its original kernel ideal and inclusion, it gives the actual
short exact sequence of module sheaves. The proof reuses the native
pullback/pushforward quotient unit. There are no quasicoherence, finiteness or
Noetherian hypotheses.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The actual structure-module map of a closed immersion is epic. -/
instance structureModuleMap_epi (f : X ⟶ Y) [IsClosedImmersion f] :
    Epi (structureModuleMap f) := by
  have h := Modules.pullbackUnitIso_homEquiv f
  change (Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
        (Modules.pushforward f).map (Modules.pullbackUnitIso f).hom =
      structureModuleMap f at h
  rw [← h]
  infer_instance

/-- The original kernel ideal, its original inclusion, and the original
structure-module quotient map. -/
abbrev idealSequence (f : X ⟶ Y) : ShortComplex Y.Modules :=
  ShortComplex.kernelSequence (structureModuleMap f)

/-- A closed immersion gives the actual short exact structure-module
sequence, with no extra hypotheses on its ambient scheme. -/
theorem idealSequence_shortExact (f : X ⟶ Y) [IsClosedImmersion f] :
    (idealSequence f).ShortExact where
  exact := ShortComplex.kernelSequence_exact (structureModuleMap f)
  epi_g := inferInstanceAs (Epi (structureModuleMap f))

end AlgebraicGeometry.Scheme.Hom
