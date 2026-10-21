/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
Native extraction from `R5Lab.Aglib.AlgebraicGeometry.Stalk.Regular`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`e6a8de660e77bebcaba3a3cb8409422e4c3b1e828d64a4e5dea6223db10c2476`.
Only image transport and open-cover descent are extracted; Scheme.RegularStalks is reused.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.RegularStalks

lemma at_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hX : RegularStalks X) (x : X) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) := by
  let := hX x
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv

lemma of_cover {X : Scheme.{u}} {ι : Type*} (Y : ι → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (hY : ∀ i, RegularStalks (Y i)) : RegularStalks X := by
  intro x
  obtain ⟨i, y, rfl⟩ := hc x
  exact at_image (f i) (hY i) y


end AlgebraicGeometry.Scheme.RegularStalks
