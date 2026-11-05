/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.IntegralOpen

/-! # Noetherian support induction for properties of original scheme maps

The property is indexed by actual morphisms into the fixed source. Its open
and closed gluing hypotheses therefore retain those maps and can carry an
original pulled-back coefficient. Only the complementary reduced closed
support is smaller; no dimension bound or finite underlying coefficient is
needed. Nilpotent reduction and the empty scheme remain explicit inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

/-- Generic integral-open production, original open/closed gluing, and actual
surjective closed reduction prove a property on a Noetherian source. All
property values refer to the original composite map into that source. -/
theorem property_of_noetherian_generic_open_closed
    {X : Scheme.{u}} [IsNoetherian X]
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (hempty : ∀ (Y : Scheme.{u}) (j : Y ⟶ X), IsEmpty Y → P j)
    (hgeneric : ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsAffine Y] [IsIntegral Y]
      (j : Y ⟶ X) [IsImmersion j],
      ∃ (U : Scheme.{u}) (a : U ⟶ Y),
        IsOpenImmersion a ∧ Nonempty U ∧ P (a ≫ j))
    (hglue : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsClosedImmersion j → IsReduced Y →
      ∀ (U : Scheme.{u}) (a : U ⟶ Y) [IsOpenImmersion a],
        P (a ≫ j) →
        P ((IdealSheafData.vanishingIdeal a.opensRange.compl).subschemeι ≫ j) → P j)
    (hreduction : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsClosedImmersion j → IsReduced Y → Surjective j → P j → P (𝟙 X)) :
    P (𝟙 X) := by
  have hrad {Y : Scheme.{u}} (Z : Closeds Y) :
      (IdealSheafData.vanishingIdeal Z).radical = IdealSheafData.vanishingIdeal Z := by
    apply Scheme.IdealSheafData.ext
    funext V
    simp only [IdealSheafData.radical_ideal, IdealSheafData.vanishingIdeal_ideal]
    exact Ideal.radical_eq_iff.mpr (PrimeSpectrum.isRadical_vanishingIdeal _)
  let Q (Z : Closeds X) : Prop := ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
    IsClosedImmersion j → IsReduced Y → Set.range j = (Z : Set X) → P j
  have hQ : ∀ Z, Q Z := by
    intro Z
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih Y j hj hred hjrange
    let : IsClosedImmersion j := hj
    let : IsReduced Y := hred
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    let : IsNoetherian Y := ⟨⟩
    by_cases hY : Nonempty Y
    · let : Nonempty Y := hY
      obtain ⟨V, hV, _, hVI⟩ := Scheme.exists_integral_affine_open_of_noetherian_reduced Y
      let : IsAffine V.toScheme := hV
      let : IsIntegral V.toScheme := hVI
      let : IsNoetherian V.toScheme := ⟨⟩
      obtain ⟨U, a, ha, hU, hP⟩ := hgeneric V.toScheme (V.ι ≫ j)
      let : IsOpenImmersion a := ha
      let b : U ⟶ Y := a ≫ V.ι
      have hb : P (b ≫ j) := by simpa only [b, Category.assoc] using hP
      let I := IdealSheafData.vanishingIdeal b.opensRange.compl
      let k : I.subscheme ⟶ X := I.subschemeι ≫ j
      have hIred : IsReduced I.subscheme :=
        IdealSheafData.subscheme_reduced_of_radical I (hrad _)
      let W : Closeds X := ⟨Set.range k, k.isClosedEmbedding.isClosed_range⟩
      have hWle : W ≤ Z := by
        rintro x ⟨z, rfl⟩
        change k z ∈ (Z : Set X)
        rw [← hjrange]
        exact ⟨I.subschemeι z, rfl⟩
      have hWne : W ≠ Z := by
        intro heq
        let s : U := Classical.choice hU
        have hx : j (b s) ∈ (W : Set X) := by
          rw [heq, ← hjrange]
          exact ⟨b s, rfl⟩
        obtain ⟨z, hz⟩ := hx
        have hz' : I.subschemeι z = b s := j.isClosedEmbedding.injective hz
        have hmem : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
        rw [IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal] at hmem
        exact hmem (hz'.symm ▸ ⟨s, rfl⟩)
      exact hglue Y j hj hred U b hb
        (ih W (lt_of_le_of_ne hWle hWne) I.subscheme k inferInstance hIred rfl)
    · exact hempty Y j (not_nonempty_iff.mp hY)
  let I := IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hIred : IsReduced I.subscheme :=
    IdealSheafData.subscheme_reduced_of_radical I (hrad _)
  have hIrange : Set.range I.subschemeι = (⊤ : Set X) :=
    (IdealSheafData.range_subschemeι I).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  have hsurj : Surjective I.subschemeι := ⟨by
    intro x
    have hx : x ∈ Set.range I.subschemeι := by rw [hIrange]; trivial
    exact hx⟩
  exact hreduction I.subscheme I.subschemeι inferInstance hIred hsurj
    (hQ ⊤ I.subscheme I.subschemeι inferInstance hIred hIrange)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
