/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompletionBaseChange
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Original ordinary completion mate for separated morphisms

The original qcqs completion theorem applies to separated morphisms.
This thin specialization retains its unchanged adjunction mate.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- Noetherian completion preserves the original ordinary separated pushforward mate. -/
theorem moduleBaseChangeMap_completion_isIso_of_isSeparated
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact p] [IsSeparated p]
    (G : Y.Modules) [G.IsQuasicoherent] :
    IsIso (moduleBaseChangeMap p
      (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))) G) :=
  moduleBaseChangeMap_completion_isIso J p G

end AlgebraicGeometry.Scheme.Modules
