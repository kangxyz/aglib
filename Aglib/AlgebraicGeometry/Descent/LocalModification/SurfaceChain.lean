/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.SupportedChain

/-!
# The supplied local surface chain, without a punctured-isomorphism premise

The native proper-birational surface theorem proves the punctured-spectrum
isomorphism. The globalization consumer retains the original terminal
cartesian square and the exact supplied length.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

open Blowup

/-- Properness of the actual supplied local surface chain gives its
punctured-isomorphism property; this is a conclusion, not an extra oracle. -/
theorem punctured_isIso_of_normalizedChain
    {X T : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hX : NormalStalks X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X))
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (upper : NormalizedPointBlowupChain p) :
    IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx) := by
  let : IsIntegral T := upper.isIntegral inferInstance
  let : IsDominant p := upper.isDominant inferInstance
  have hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap p)) :=
    upper.functionFieldMap_isIso inferInstance
  rw [fromSpecStalk_preimage_pointComplement]
  exact isIso_restrict_punctured_stalkSpec X hX hdim x p hff

/-- A prescribed proper normalized-point chain on the original stalk of a
normal Noetherian surface extends to an actual global chain of the same
length, with the original cartesian terminal comparison and no changes off
the original closed nongeneric point. -/
theorem exists_surface_supported_normalizedChain
    {X T : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hX : NormalStalks X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (upper : NormalizedPointBlowupChain p) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (lower : NormalizedPointBlowupChain f)
      (a : T ⟶ Z), IsProper f ∧ lower.length = upper.length ∧
      IsPullback a p f (X.fromSpecStalk x) ∧ IsIso (f ∣_ pointComplement x hx) := by
  exact exists_supported_normalizedChain_of_punctured hX x hx hxη p upper
    (punctured_isIso_of_normalizedChain hX hdim x hx p upper)

/-- If the supplied local terminal scheme and unchanged complement are
regular, the actual global chain has regular integral normal source and its
original birational field map. Both terminal pullback projections are retained. -/
theorem exists_regular_surface_supported_normalizedChain
    {X T : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (hX : NormalStalks X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : IsClosed ({x} : Set X)) (hxη : x ≠ genericPoint X)
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (upper : NormalizedPointBlowupChain p) (hT : RegularStalks T)
    (hU : RegularStalks (pointComplement x hx).toScheme) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (lower : NormalizedPointBlowupChain f)
      (hZ : IsIntegral Z) (hdom : IsDominant f),
      letI := hZ
      letI := hdom
      IsProper f ∧ lower.length = upper.length ∧ NormalStalks Z ∧ RegularStalks Z ∧
      IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) ∧
      IsIso (f ∣_ pointComplement x hx) ∧
      ∃ E : T ≅ pullback f (X.fromSpecStalk x),
        E.hom ≫ pullback.snd f (X.fromSpecStalk x) = p ∧
        E.hom ≫ pullback.fst f (X.fromSpecStalk x) ≫ f = p ≫ X.fromSpecStalk x := by
  obtain ⟨Z, f, lower, a, hf, hlen, H, hfU⟩ :=
    exists_surface_supported_normalizedChain hX hdim x hx hxη p upper
  let hZ : IsIntegral Z := lower.isIntegral inferInstance
  let : IsIntegral Z := hZ
  let hdom : IsDominant f := lower.isDominant inferInstance
  let : IsDominant f := hdom
  have hreg : RegularStalks Z := regularStalks_of_local_replacement x hx hU hT a p f H hfU
  refine ⟨Z, f, lower, hZ, hdom, hf, hlen, lower.normalStalks hX, hreg,
    lower.functionFieldMap_isIso inferInstance, hfU, H.isoPullback, H.isoPullback_hom_snd, ?_⟩
  rw [H.isoPullback_hom_fst_assoc]
  exact H.w

end AlgebraicGeometry.Scheme.LocalModification
