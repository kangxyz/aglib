/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.Ambient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Values

/-! # Geometric constructibility for the original modulus-one presentation

Every actual coefficient killed by one is zero, hence finite locally
constant. The original filtered producer therefore already has geometric
constructible and ambient finitely presentable stages at this modulus,
including on an empty scheme. No positive-modulus result beyond one is
asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u})

/-- Every original modulus-one coefficient is finite locally constant. -/
theorem coefficient_one_isFiniteLocallyConstant (F : BoundedPresentation.Coefficient X 1) :
    IsFiniteLocallyConstant F.obj := by
  apply FiniteColimits.isFiniteLocallyConstant_of_isZero
  rw [IsZero.iff_id_eq_zero]
  have h : 1 • 𝟙 F.obj = 0 := F.property
  simpa only [one_nsmul] using h

/-- The modulus-one stages are geometrically constructible. -/
theorem coefficient_one_isConstructible (F : BoundedPresentation.Coefficient X 1) :
    IsConstructible F.obj :=
  isConstructible_of_isFiniteLocallyConstant (coefficient_one_isFiniteLocallyConstant X F)

/-- The actual bounded-presentation diagram and cocone have constructible,
ambient finitely presentable stages at modulus one. -/
theorem exists_filtered_presentation_one_constructible
    (F : AbelianSheaf.{u, u + 1} X) (hF : 1 • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ BoundedPresentation.Coefficient X 1)
      (ι : D ⋙ BoundedPresentation.inclusion X 1 ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, BoundedPresentation.finiteColimitStages X 1 (D.obj i) ∧
          IsFinitelyPresentable.{u + 1} (D.obj i).obj ∧ IsConstructible (D.obj i).obj := by
  obtain ⟨I, hI, hfiltered, D, ι, hcolimit, hstage⟩ :=
    exists_filtered_presentation_ambient_finitelyPresentable X 1 F hF
  let := hI
  have : IsFiltered I := hfiltered
  exact ⟨I, hI, hfiltered, D, ι, hcolimit,
    fun i => ⟨(hstage i).1, (hstage i).2, coefficient_one_isConstructible X (D.obj i)⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
