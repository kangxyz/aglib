/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Effective epimorphism descent in a category over a base

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.DualIsogeny`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 118–161.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory
namespace CategoryTheory.Over
variable {C : Type u} [Category.{v} C] {S : C}
variable {X Y W : Over S} (f : X ⟶ Y) [EffectiveEpi f.left]

omit [EffectiveEpi f.left] in
/-- The over-category cocycle is an actual underlying cocycle: equality after
f forces the two test maps to have the same base structure. -/
theorem effectiveEpiCocycle (e : X ⟶ W)
    (h : ∀ {Z : Over S} (a b : Z ⟶ X), a ≫ f = b ≫ f → a ≫ e = b ≫ e)
    {Z : C} (a b : Z ⟶ X.left) (hab : a ≫ f.left = b ≫ f.left) :
    a ≫ e.left = b ≫ e.left := by
  have hs : b ≫ X.hom = a ≫ X.hom := by
    simpa only [Category.assoc, Over.w] using
      congrArg (fun k : Z ⟶ Y.left => k ≫ Y.hom) hab.symm
  let aa : Over.mk (a ≫ X.hom) ⟶ X := Over.homMk a rfl
  let bb : Over.mk (a ≫ X.hom) ⟶ X := Over.homMk b hs
  have he := h aa bb (Over.OverMorphism.ext hab)
  exact congrArg (fun k => k.left) he

/-- Actual descent in the over category from the existing effective epimorphism. -/
def effectiveEpiDesc (e : X ⟶ W)
    (h : ∀ {Z : Over S} (a b : Z ⟶ X), a ≫ f = b ≫ f → a ≫ e = b ≫ e) : Y ⟶ W :=
  Over.homMk (EffectiveEpi.desc f.left e.left (effectiveEpiCocycle f e h)) (by
    apply (cancel_epi f.left).1
    rw [← Category.assoc, EffectiveEpi.fac, Over.w, Over.w])

@[reassoc] theorem effectiveEpiDesc_fac (e : X ⟶ W)
    (h : ∀ {Z : Over S} (a b : Z ⟶ X), a ≫ f = b ≫ f → a ≫ e = b ≫ e) :
    f ≫ effectiveEpiDesc f e h = e := by
  apply Over.OverMorphism.ext
  exact EffectiveEpi.fac f.left e.left (effectiveEpiCocycle f e h)

/-- An effective epimorphism of underlying objects is effective over the base.
For schemes the needed instance is already proved in pinned mathlib for fpqc maps. -/
theorem effectiveEpi_of_left : EffectiveEpi f := by
  refine ⟨⟨{ desc := fun e h => effectiveEpiDesc f e h,
              fac := fun e h => effectiveEpiDesc_fac f e h,
              uniq := ?_ }⟩⟩
  intro W e h m hm
  apply Over.OverMorphism.ext
  exact EffectiveEpi.uniq f.left e.left (effectiveEpiCocycle f e h) m.left
    (congrArg (fun k => k.left) hm)

end CategoryTheory.Over
