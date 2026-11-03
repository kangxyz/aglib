/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.NormalizedPointLocalization

/-!
# Transport of the prescribed chain through an actual base isomorphism

Centres are transported by the given scheme isomorphism. The lower chain
uses literal normalized point blowups, and its terminal isomorphism retains
the original structural triangle and the exact length.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Transport a native chain through the given base isomorphism, preserving
its centres, length, and terminal structural map rather than just its source. -/
theorem NormalizedPointBlowupChain.transportIso
    {Y T : Scheme.{u}} {g : T ⟶ Y} (upper : NormalizedPointBlowupChain g) :
    ∀ (X : Scheme.{u}) [IsIntegral X] (e : Y ≅ X),
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (lower : NormalizedPointBlowupChain f)
        (E : T ≅ Z), lower.length = upper.length ∧ E.hom ≫ f = g ≫ e.hom := by
  induction upper with
  | refl Y =>
    intro X hX e
    exact ⟨X, 𝟙 X, .refl X, e, rfl, by simp⟩
  | @cons Y T hY y hy hyη t tail ih =>
    intro X hX e
    let := hX
    have hx : IsClosed ({e.hom y} : Set X) := by
      simpa only [Set.image_singleton] using e.hom.isClosedMap _ hy
    have hxη : e.hom y ≠ genericPoint X := by
      intro he
      apply hyη
      apply e.hom.injective
      exact he.trans (Scheme.map_genericPoint_of_isDominant Y e.hom).symm
    let sX := normalizedPointBlowupMap X (e.hom y) hx hxη
    let sY := normalizedPointBlowupMap Y y hy hyη
    let X₁ := normalizedPointBlowup X (e.hom y) hx hxη
    let Y₁ := normalizedPointBlowup Y y hy hyη
    let : IsIntegral X₁ := normalizedPointBlowup_isIntegral X (e.hom y) hx hxη
    let E₀ := normalizedPointLocalizationIso e.hom y hy hyη hx hxη
    let E₁ : Y₁ ≅ X₁ := E₀ ≪≫ asIso (pullback.fst sX e.hom)
    have hE₁ : E₁.hom ≫ sX = sY ≫ e.hom := by
      change (E₀.hom ≫ pullback.fst sX e.hom) ≫ sX = sY ≫ e.hom
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ e.hom)
        (normalizedPointLocalizationIso_hom_snd e.hom y hy hyη hx hxη)
    obtain ⟨Z, f, lower, E, hlen, hE⟩ := ih X₁ E₁
    refine ⟨Z, f ≫ sX, .cons (e.hom y) hx hxη f lower, E, ?_, ?_⟩
    · simpa only [NormalizedPointBlowupChain.length] using congrArg (· + 1) hlen
    · rw [← Category.assoc, hE, Category.assoc, hE₁]
      simp only [Category.assoc]
      rfl

end AlgebraicGeometry.Scheme.Blowup
