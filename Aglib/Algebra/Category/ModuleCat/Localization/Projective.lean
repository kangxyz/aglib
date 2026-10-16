/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Projectivity of native scalar extension on a basic free-locus neighbourhood

If a basic open lies in a finitely presented module's native free locus,
its original scalar extension to that basic-open ring is projective.
The native localized-module/tensor equivalence and the existing
scalar-extension/tensor comparison retain the actual module objects.
No Noetherianity or reducedness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module
open scoped TensorProduct

namespace ModuleCat

universe u v

variable {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R)

/-- The original free locus is detected by the unchanged scalar-extension object
at the prime. No finite-presentation hypothesis is needed for this comparison. -/
theorem mem_freeLocus_iff_free_extendScalars_atPrime (p : PrimeSpectrum R) :
    p ∈ Module.freeLocus R M ↔
      Module.Free (Localization.AtPrime p.asIdeal)
        ((extendScalars (algebraMap R (Localization.AtPrime p.asIdeal))).obj M) := by
  rw [Module.mem_freeLocus_iff_tensor p (Localization.AtPrime p.asIdeal)]
  let e := (extendScalarsAlgebraObjIso R (Localization.AtPrime p.asIdeal) M).toLinearEquiv
  constructor
  · intro h
    let : Module.Free (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] M) := h
    exact Module.Free.of_equiv e.symm
  · intro h
    let : Module.Free (Localization.AtPrime p.asIdeal)
        ((extendScalars (algebraMap R (Localization.AtPrime p.asIdeal))).obj M) := h
    exact Module.Free.of_equiv e

variable [Module.FinitePresentation R M]

/-- An actual basic open in the original free locus gives projectivity of the unchanged
native scalar extension to its localized ring. -/
theorem projective_extendScalars_away_of_basicOpen_subset_freeLocus (r : R)
    (h : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R M) :
    Module.Projective (Localization.Away r)
      ((extendScalars (algebraMap R (Localization.Away r))).obj M) := by
  let : Module.Projective (Localization.Away r) (LocalizedModule.Away r M) :=
    Module.basicOpen_subset_freeLocus_iff.mp h
  exact Module.Projective.of_equiv'
    ((LocalizedModule.equivTensorProduct (Submonoid.powers r) M).trans
      (extendScalarsAlgebraObjIso R (Localization.Away r) M).symm.toLinearEquiv)

end ModuleCat
