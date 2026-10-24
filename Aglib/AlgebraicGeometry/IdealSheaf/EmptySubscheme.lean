/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# The empty closed subscheme

For a closed subscheme `W ⊆ X` of an arbitrary scheme (`W : X.IdealSheafData`):

* `Scheme.IdealSheafData.isEmpty_subscheme_iff`: `W` is empty exactly when its ideal sheaf is the
  unit ideal sheaf, `W = ⊤`. The points of `W` are those of its support
  (`IdealSheafData.range_subschemeι`), and the support is empty exactly for `⊤`
  (`IdealSheafData.support_eq_bot_iff`).
* `Scheme.IdealSheafData.isZero_quotientModule_iff`: the structure module `𝒪_W = 𝒪_X / I_W`
  (`quotientModule`) is zero exactly when `W = ⊤`. Through `𝒪_X / I_W ≅ i_* 𝒪_W`
  (`quotientModuleIsoPushforward`): every module on the empty scheme is zero (all stalks vanish,
  `Scheme.Modules.isZero_iff_stalks`); conversely, the global sections of `i_* 𝒪_W` are the ring
  `Γ(W, ⊤)`, which is nontrivial when `W` has a point.

Present consumer: the nonvanishing of the Hilbert polynomial of a nonempty closed subscheme of
`P^n_K` (`HilbertScheme/Nonempty`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **A closed subscheme is empty exactly when its ideal sheaf is the unit ideal sheaf.** -/
theorem isEmpty_subscheme_iff (W : X.IdealSheafData) : IsEmpty W.subscheme ↔ W = ⊤ := by
  rw [← support_eq_bot_iff, ← TopologicalSpace.Closeds.coe_eq_empty, ← range_subschemeι,
    Set.range_eq_empty_iff]

/-- A closed subscheme is nonempty exactly when its ideal sheaf is not the unit ideal sheaf. -/
theorem nonempty_subscheme_iff (W : X.IdealSheafData) : Nonempty W.subscheme ↔ W ≠ ⊤ := by
  rw [← not_isEmpty_iff, isEmpty_subscheme_iff]

/-- The structure module of an empty closed subscheme is zero. -/
theorem isZero_quotientModule_of_isEmpty (W : X.IdealSheafData) [IsEmpty W.subscheme] :
    IsZero W.quotientModule := by
  have h0 : IsZero (SheafOfModules.unit W.subscheme.ringCatSheaf) :=
    (Scheme.Modules.isZero_iff_stalks _).mpr fun x => (IsEmpty.false x).elim
  exact ((Scheme.Modules.pushforward W.subschemeι).map_isZero h0).of_iso
    W.quotientModuleIsoPushforward

-- The sections of the pushed-forward structure sheaf are the ring sections of `W` only after
-- unfolding `SheafOfModules.unit` and the pushforward.
set_option backward.isDefEq.respectTransparency false in
/-- A closed subscheme whose structure module is zero is empty: the global sections of
`i_* 𝒪_W ≅ 𝒪_X / I_W` form the ring `Γ(W, ⊤)`, which is nontrivial when `W` has a point. -/
theorem isEmpty_subscheme_of_isZero_quotientModule (W : X.IdealSheafData)
    (h : IsZero W.quotientModule) : IsEmpty W.subscheme := by
  by_contra hne
  obtain ⟨w⟩ := not_isEmpty_iff.mp hne
  have h1 : IsZero ((Scheme.Modules.pushforward W.subschemeι).obj
      (SheafOfModules.unit W.subscheme.ringCatSheaf)) :=
    h.of_iso W.quotientModuleIsoPushforward.symm
  have h2 := (PresheafOfModules.evaluation _ (op (⊤ : X.Opens))).map_isZero
    ((SheafOfModules.forget X.ringCatSheaf).map_isZero h1)
  have h3 := ModuleCat.isZero_iff_subsingleton.mp h2
  have : Nonempty ↥(W.subschemeι ⁻¹ᵁ (⊤ : X.Opens)) :=
    ⟨⟨w, show W.subschemeι w ∈ (⊤ : X.Opens) from trivial⟩⟩
  have h4 : Subsingleton Γ(W.subscheme, W.subschemeι ⁻¹ᵁ (⊤ : X.Opens)) := h3
  exact not_subsingleton _ h4

/-- **The structure module of a closed subscheme is zero exactly when the subscheme is empty**,
that is, when its ideal sheaf is the unit ideal sheaf. -/
theorem isZero_quotientModule_iff (W : X.IdealSheafData) : IsZero W.quotientModule ↔ W = ⊤ := by
  rw [← isEmpty_subscheme_iff]
  exact ⟨W.isEmpty_subscheme_of_isZero_quotientModule, fun _ =>
    W.isZero_quotientModule_of_isEmpty⟩

end AlgebraicGeometry.Scheme.IdealSheafData
