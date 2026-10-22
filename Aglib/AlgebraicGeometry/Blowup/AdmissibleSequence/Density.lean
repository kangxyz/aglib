/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.SchematicDensity

/-!
# Schematic density along actual admissible sequences

Density is propagated through the recorded native blowup steps and source
isomorphisms, not through arbitrary proper maps or refinement comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- A quasi-compact schematically dense protected open remains schematically
dense along an actual admissible sequence. No Noetherian assumption is needed. -/
theorem preimage_open_isSchemeTheoreticallyDominant {X Y : Scheme.{u}}
    {U : X.Opens} {β : Y ⟶ X} (hβ : AdmissibleSequence U β)
    [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι] :
    IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι := by
  induction hβ with
  | id => exact inferInstanceAs (IsSchemeTheoreticallyDominant U.ι)
  | @step T δ hδ J B hJ ih =>
      let : QuasiCompact (δ ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (isPullback_morphismRestrict δ U) inferInstance
      let : IsSchemeTheoreticallyDominant (δ ⁻¹ᵁ U).ι := ih
      exact B.preimage_open_isSchemeTheoreticallyDominant (δ ⁻¹ᵁ U)
  | @iso T T' δ hδ e ih =>
      let : QuasiCompact (δ ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (isPullback_morphismRestrict δ U) inferInstance
      let : IsSchemeTheoreticallyDominant (δ ⁻¹ᵁ U).ι := ih
      have h : IsSchemeTheoreticallyDominant (e.hom ⁻¹ᵁ (δ ⁻¹ᵁ U)).ι :=
        IsSchemeTheoreticallyDominant.of_isPullback
          (isPullback_morphismRestrict e.hom (δ ⁻¹ᵁ U))
      exact h

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
