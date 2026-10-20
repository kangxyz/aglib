/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Immersion criteria for unramified morphisms

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/Immersions.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `752511a82a47baae2b8e8008c0b34d8e5a81d0d08260f01fb43626a1522bc962`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry

/-- A finite unramified universally injective morphism is a closed immersion.
Universal injectivity, not merely injectivity of the underlying point map, is
what makes its open diagonal an isomorphism. -/
theorem IsClosedImmersion.of_finite_formallyUnramified_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [FormallyUnramified f]
    [UniversallyInjective f] : IsClosedImmersion f := by
  let : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  let : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono f).mpr ⟨inferInstance, inferInstance⟩

/-- The standard diagonal criterion: a morphism whose composite is an open
immersion is itself an open immersion when the following map is unramified. -/
theorem IsOpenImmersion.of_comp_formallyUnramified {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [IsOpenImmersion (f ≫ g)]
    [LocallyOfFiniteType g] [FormallyUnramified g] : IsOpenImmersion f := by
  let : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro A B h ⟨hft, hfu⟩
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal h))
  exact MorphismProperty.of_postcomp _
    (W' := (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})) f g
    ⟨inferInstance, inferInstance⟩ inferInstance

/-- Every exact section of an unramified morphism locally of finite type is
an open immersion. This will apply to the original-field node sections. -/
theorem IsOpenImmersion.of_section_formallyUnramified {X S : Scheme.{u}}
    (p : S ⟶ X) (s : X ⟶ S) (h : p ≫ s = 𝟙 S)
    [LocallyOfFiniteType s] [FormallyUnramified s] : IsOpenImmersion p := by
  let : IsOpenImmersion (p ≫ s) := by rw [h]; infer_instance
  exact IsOpenImmersion.of_comp_formallyUnramified p s

end AlgebraicGeometry
