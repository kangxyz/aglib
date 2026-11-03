/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.FactorReplacement
public import Aglib.AlgebraicGeometry.Normalization.ProperBirational

/-!
# Finite normalization forced by a specified local terminal factor

The proper normal birational model is constructed by actual factor
replacement, rather than supplied as a globalization premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

/-- An actual proper normal integral stalk modification, with a specified
factor into the proper global target, forces that target's literal generic
normalization to be finite. The global target and original base are unchanged. -/
theorem genericNormalization_isFinite_of_stalk_factor
    {X B T : Scheme.{u}} [IsIntegral X] [IsIntegral B] [IsIntegral T]
    [IsLocallyNoetherian X] (hX : NormalStalks X) (hT : NormalStalks T)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (b : B ⟶ X) [IsProper b] (hb : IsIso (b ∣_ pointComplement x hx))
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p] [IsDominant p]
    (hp : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx))
    (a : T ⟶ B) (ha : a ≫ b = p ≫ X.fromSpecStalk x) :
    IsFinite (B.fromSpecStalk (genericPoint B)).fromNormalization := by
  obtain ⟨R, r, hr, hrb, _hra⟩ := exists_stalkReplacement_factor x hx b hb p hp a ha
  let : IsIntegral R.Y := isIntegral_of_local_replacement x hx hxη hX hT
    R.a p R.h R.square R.isoRestriction
  have hR : NormalStalks R.Y := normalStalks_of_local_replacement x hx hX hT
    R.a p R.h R.square R.isoRestriction
  let : IsProper r := hr
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian b
  let U := pointComplement x hx
  let V := b ⁻¹ᵁ U
  let : IsIso (b ∣_ U) := hb
  let : Nonempty U := ⟨⟨genericPoint X, hxη.symm⟩⟩
  let : Nonempty V := ⟨inv (b ∣_ U) ⟨genericPoint X, hxη.symm⟩⟩
  have hrV : IsIso (r ∣_ V) := by
    have H : IsIso ((r ≫ b) ∣_ U) := by rw [hrb]; exact R.isoRestriction
    rw [morphismRestrict_comp] at H
    let := H
    exact IsIso.of_isIso_comp_right (r ∣_ V) (b ∣_ U)
  let : IsDominant r := isDominant_of_isIso_restrict r V hrV
  have hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap r)) :=
    functionFieldMap_isIso_of_isIso_restrict r V hrV
  exact genericNormalization_isFinite_of_proper_birational r hR hff

end AlgebraicGeometry.Scheme.LocalModification
