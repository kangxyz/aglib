/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification
public import Aglib.AlgebraicGeometry.Stalk.Dimension

/-!
# Dimension through the original supported localization square

At the original centre, the native localization projection identifies actual
stalks. Away from it, the original restriction does so. This is the same
stalkwise proof extracted once from ProjectiveSurfaceChain, for any bound.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

/-- Dimension is transported through the SAME supported local square.
No integrality, properness, normality or Noetherian hypothesis is needed. -/
theorem topologicalKrullDim_le_of_local_replacement
    {X Y T : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x)) (f : Y ⟶ X)
    (H : IsPullback a p f (X.fromSpecStalk x))
    (hU : IsIso (f ∣_ pointComplement x hx))
    (d : WithBot ℕ∞) (hdX : topologicalKrullDim X ≤ d)
    (hdT : topologicalKrullDim T ≤ d) : topologicalKrullDim Y ≤ d := by
  rw [topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro z
  by_cases hz : f z = x
  · obtain ⟨t, rfl, _⟩ := exists_preimage_over_center x a p f H z hz
    let : IsIso (a.stalkMap t) :=
      isIso_stalkMap_localization_projection x a p f H t
    have hd : ringKrullDim (T.presheaf.stalk t) ≤ d := by
      have ht := le_iSup (fun t : T => ringKrullDim (T.presheaf.stalk t)) t
      rw [← topologicalKrullDim_eq_iSup_stalk T] at ht
      exact ht.trans hdT
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (a.stalkMap t)).commRingCatIsoToRingEquiv).le.trans hd
  · let U := pointComplement x hx
    let : IsIso (f ∣_ U) := hU
    let z' : (f ⁻¹ᵁ U).toScheme := ⟨z, hz⟩
    have hz' : IsIso ((f ∣_ U).stalkMap z') := inferInstance
    let : IsIso (f.stalkMap z) :=
      ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap f U z')).mp hz'
    have hd : ringKrullDim (X.presheaf.stalk (f z)) ≤ d := by
      have ht := le_iSup (fun t : X => ringKrullDim (X.presheaf.stalk t)) (f z)
      rw [← topologicalKrullDim_eq_iSup_stalk X] at ht
      exact ht.trans hdX
    exact (ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap z)).symm.commRingCatIsoToRingEquiv).le.trans hd

end AlgebraicGeometry.Scheme.LocalModification
