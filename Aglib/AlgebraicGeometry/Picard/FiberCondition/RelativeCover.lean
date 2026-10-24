/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.OpenSubfunctor

/-!
# Relative covers by fiber conditions

For a fiber condition `C` and a family `D j` of fiber conditions, if at every point where `C`
holds some `D j` holds, then the opens of the conjunctions `C ⊓ D j` cover the open of `C`:
`⨆ j, (C ⊓ D j).opens ξ = C.opens ξ` for every section `ξ` of `Pic_{X/S,(fppf)}` over a locally
Noetherian `T` (`iSup_opens_inf_eq`). This is the relative form of `iSup_opens_eq_top`, used for
Kleiman's nested cover: for a section of `P` over `T`, the union over `m` of the `P^φ_m ×_P T` is
`T^φ = P^φ ×_P T` (Kleiman states it for `T → P^φ`, where the union is `T`; *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 29). The pointwise test is on a flat representative
through each point (`exists_flat_app_eq`), as in `iSup_opens_eq_top`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.FiberCondition

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

/-- **Relative cover** (Kleiman, arXiv:math/0504020v1, p. 29): if every point where `C` holds
satisfies some `D j`, then the opens of the conjunctions `C ⊓ D j` cover the open of `C`. -/
theorem iSup_opens_inf_eq {ι : Type*} (D : ι → FiberCondition p)
    (hD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      C.Holds T a t → ∃ j, (D j).Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ⨆ j, (C ⊓ D j).opens ξ = C.opens ξ := by
  apply le_antisymm
  · exact iSup_le fun j => (C.opens_inf (D j) ξ).le.trans inf_le_left
  · intro t ht
    obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
    have hC := (C.holdsAt_iff ξ _ a ha v).mp ht
    obtain ⟨j, hj⟩ := hD _ a v hC
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ((C ⊓ D j).holdsAt_iff ξ _ a ha v).mpr ⟨hC, hj⟩⟩

end AlgebraicGeometry.Scheme.RelativePicard.FiberCondition
