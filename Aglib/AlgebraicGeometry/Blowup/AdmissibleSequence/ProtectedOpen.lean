/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence

/-!
# Shrinking the protected open of an actual blowup sequence

Protection passes to smaller opens by restricting each actual unit centre.
No equality with an inverse-image open is required.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- An actual sequence protecting an open also protects every smaller open. -/
theorem mono {X Y : Scheme.{u}} {U V : X.Opens} {β : Y ⟶ X}
    (hβ : AdmissibleSequence U β) (hVU : V ≤ U) : AdmissibleSequence V β := by
  induction hβ with
  | id => exact .id
  | @step T δ hδ J B hJ ih =>
      apply AdmissibleSequence.step ih J B
      have hle : δ ⁻¹ᵁ V ≤ δ ⁻¹ᵁ U := fun _ hx => hVU hx
      rw [← T.homOfLE_ι hle, IdealSheafData.comap_comp, hJ,
        IdealSheafData.comap_top]
  | iso hδ e ih => exact .iso ih e

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
