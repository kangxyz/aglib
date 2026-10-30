/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Nonzero sections of the original line bundle on a reduced scheme

Empty nonvanishing forces every coefficient in an actual local unit frame
to vanish. Native reducedness and sheaf section extensionality then give
zero. In particular, an effective bundle's original nonzero section has a
nonempty geometric nonvanishing open.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a reduced scheme, an original line-bundle section with empty
nonvanishing open is zero. -/
theorem eq_zero_of_nonvanishingOpen_eq_bot {X : Scheme.{u}} [IsReduced X]
    (L : LineBundle X) (s : Γ(L.val, ⊤)) (hs : nonvanishingOpen L s = ⊥) : s = 0 := by
  let M : X.Modules := L.val
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj L.val)
    ⊤ s 0
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  have hc : chartSectionEquiv X L.val U e U le_rfl
      (L.val.val.map (homOfLE le_top).op s) = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    rw [← inter_nonvanishingOpen L s U e, hs, inf_bot_eq]
  have hz : L.val.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0 := by
    apply (chartSectionEquiv X L.val U e U le_rfl).injective
    exact hc.trans (map_zero _).symm
  have hz' : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0 := hz
  change M.presheaf.germ ⊤ x hx s = M.presheaf.germ ⊤ x hx 0
  rw [← M.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hxU s,
    hz', map_zero, map_zero]

/-- A nonzero original section has a nonempty nonvanishing open on a
reduced scheme; no integral or Noetherian hypothesis is required. -/
theorem nonempty_nonvanishingOpen_of_ne_zero {X : Scheme.{u}} [IsReduced X]
    (L : LineBundle X) (s : Γ(L.val, ⊤)) (hs : s ≠ 0) :
    (nonvanishingOpen L s : Set X).Nonempty := by
  by_contra h
  have hbot : nonvanishingOpen L s = ⊥ := by rwa [← Opens.not_nonempty_iff_eq_bot]
  exact hs (eq_zero_of_nonvanishingOpen_eq_bot L s hbot)

end AlgebraicGeometry.Scheme.Modules.Invertible
