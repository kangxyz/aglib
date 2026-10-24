/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Cohomologous
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# The pulled-back unit cocycle

Let `f : X ⟶ Y` be a morphism of schemes, `c` a unit cocycle on an open cover `U` of `Y`, and
`U'` a family of opens of `X` with `f⁻¹(U i) = U' i`. The images under `f` of the transition
units of `c` form a unit cocycle on `U'` (`UnitCocycle.pullbackCocycle`). By
`UnitCocycle.pullbackIso`, the pullback along `f` of the line bundle glued from `c` is the line
bundle glued from `pullbackCocycle` (`UnitCocycle.classOf_pullbackLineBundle`).

`ProjectiveSpace.FromSections.pullbackCocycle` is the case `U' i = f⁻¹(U i)`
(`hU := fun _ => rfl`). The general family is needed when `f⁻¹(U i) = U' i` holds only
propositionally, as for `i⁻¹(p⁻¹(U j)) = U j` along a split thickening.
-/

@[expose] public section

noncomputable section


open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} {U : ι → Y.Opens} {U' : ι → X.Opens}

/-- Restricting after `f.appLE` is `f.appLE` after restricting. -/
theorem sectionRestrict_appLE {W₁ : Y.Opens} {V₁ V : X.Opens} (e₁ : V₁ ≤ f ⁻¹ᵁ W₁)
    (h : V ≤ V₁) {W : Y.Opens} (hW : W ≤ W₁) (hV : V ≤ f ⁻¹ᵁ W) (s : Γ(Y, W₁)) :
    sectionRestrict X h ((f.appLE W₁ V₁ e₁).hom s) =
      (f.appLE W V hV).hom (sectionRestrict Y hW s) := by
  have h₁ := f.appLE_map e₁ (homOfLE h).op
  have h₂ := f.map_appLE hV (homOfLE hW).op
  have e := congrArg (fun φ : Γ(Y, W₁) ⟶ Γ(X, V) => φ.hom s) (h₁.trans h₂.symm)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

variable (c : UnitCocycle U) (hU : ∀ i, f ⁻¹ᵁ U i = U' i)

/-- The images under `f` of the transition units of `c`, a unit cocycle on `U'`. -/
def pullbackCocycle : UnitCocycle U' where
  transition i j := Units.map (f.appLE (U i ⊓ U j) (U' i ⊓ U' j)
    (inf_le_preimage_inf hU i j)).hom.toMonoidHom (c.transition i j)
  cocycle i j k V hi hj hk := by
    have hWi : U i ⊓ U j ⊓ U k ≤ U i := inf_le_left.trans inf_le_left
    have hWj : U i ⊓ U j ⊓ U k ≤ U j := inf_le_left.trans inf_le_right
    have hWk : U i ⊓ U j ⊓ U k ≤ U k := inf_le_right
    have hV : V ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) :=
      le_inf (le_inf (hi.trans (hU i).ge) (hj.trans (hU j).ge)) (hk.trans (hU k).ge)
    have e := congrArg (fun w : (Γ(Y, U i ⊓ U j ⊓ U k))ˣ =>
      (f.appLE (U i ⊓ U j ⊓ U k) V hV).hom (w : Γ(Y, U i ⊓ U j ⊓ U k)))
      (c.cocycle i j k (U i ⊓ U j ⊓ U k) hWi hWj hWk)
    apply Units.ext
    change sectionRestrict X (le_inf hi hj) ((f.appLE (U i ⊓ U j) (U' i ⊓ U' j)
          (inf_le_preimage_inf hU i j)).hom (c.transition i j : Γ(Y, U i ⊓ U j))) *
        sectionRestrict X (le_inf hj hk) ((f.appLE (U j ⊓ U k) (U' j ⊓ U' k)
          (inf_le_preimage_inf hU j k)).hom (c.transition j k : Γ(Y, U j ⊓ U k))) =
      sectionRestrict X (le_inf hi hk) ((f.appLE (U i ⊓ U k) (U' i ⊓ U' k)
          (inf_le_preimage_inf hU i k)).hom (c.transition i k : Γ(Y, U i ⊓ U k)))
    rw [sectionRestrict_appLE f _ (le_inf hi hj) (le_inf hWi hWj) hV,
      sectionRestrict_appLE f _ (le_inf hj hk) (le_inf hWj hWk) hV,
      sectionRestrict_appLE f _ (le_inf hi hk) (le_inf hWi hWk) hV, ← map_mul]
    exact e

/-- The transition units of `pullbackCocycle` are the images under `f` of those of `c`. -/
theorem transitionPullback_pullbackCocycle : TransitionPullback f c (c.pullbackCocycle f hU) :=
  fun _ _ _ => rfl

/-- The pullback of the line bundle glued from `c` is glued from the pulled-back cocycle. -/
theorem classOf_pullbackLineBundle (hYU : iSup U = ⊤) :
    classOf X (pullbackLineBundle f (c.lineBundle hYU)) =
      classOf X ((c.pullbackCocycle f hU).lineBundle (iSup_eq_top_of_preimage hU hYU)) :=
  (class_eq_iff X _ _).mpr
    ⟨c.pullbackIso f (c.pullbackCocycle f hU) hU (transitionPullback_pullbackCocycle f c hU) hYU⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
