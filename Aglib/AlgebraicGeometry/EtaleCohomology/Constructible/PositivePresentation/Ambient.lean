/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.BoundedPresentation
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure

/-! # Ambient compactness of the original bounded-presentation stages

The actual bounded-coefficient inclusion preserves the original colimits.
Ambient finite presentability is closed under these finite colimits, and
the actual affine-etale free generators are already ambient finitely
presentable. Thus every stage of the frozen bounded-presentation producer
is finitely presentable in the original abelian sheaf category.

This algebraic assertion holds for every modulus, including zero. It does
not assert geometric constructibility of the zero-modulus generators.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

variable (X : Scheme.{u}) (n : ℕ)

/-- An actual finite-colimit stage is finitely presentable in the original
ambient abelian sheaf category, at the coefficient/index size u+1. -/
theorem finiteColimitStage_isFinitelyPresentable
    (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) :
    IsFinitelyPresentable.{u + 1} F.obj := by
  let κ : Cardinal.{u + 1} := Cardinal.aleph0
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    (isCardinalPresentable.{u + 1, u + 1, u + 2}
      (AbelianSheaf.{u, u + 1} X) κ).inverseImage
      (BoundedPresentation.inclusion X n)
  have hgen : BoundedPresentation.generators X n ≤ Q := by
    rintro F ⟨U⟩
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
      change IsAffine (Spec U.left.unop)
      infer_instance
    change IsFinitelyPresentable.{u + 1}
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
        ((Scheme.AffineEtale.Spec X).obj U))
    exact qcqs_freeZModRepresentable_isFinitelyPresentable n _
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le κ ?_ hgen
    intro J _ hJ
    have : (isCardinalPresentable.{u + 1, u + 1, u + 2}
        (AbelianSheaf.{u, u + 1} X) κ).IsClosedUnderColimitsOfShape J :=
      isClosedUnderColimitsOfShape_isCardinalPresentable.{u + 1, u + 1, u + 1, u + 1, u + 2}
        (AbelianSheaf.{u, u + 1} X) hJ
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

/-- The original bounded-presentation producer has ambient finitely
presentable stages, retaining its actual diagram and original cocone.
No geometric constructibility statement is included for modulus zero. -/
theorem exists_filtered_presentation_ambient_finitelyPresentable
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ BoundedPresentation.Coefficient X n)
      (ι : D ⋙ BoundedPresentation.inclusion X n ⟶ (Functor.const I).obj F),
      Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, BoundedPresentation.finiteColimitStages X n (D.obj i) ∧
          IsFinitelyPresentable.{u + 1} (D.obj i).obj := by
  obtain ⟨I, hI, hfiltered, D, ι, hcolimit, hstage⟩ :=
    BoundedPresentation.exists_filtered_presentation X n F hF
  let := hI
  have : IsFiltered I := hfiltered
  exact ⟨I, hI, hfiltered, D, ι, hcolimit,
    fun i => ⟨hstage i, finiteColimitStage_isFinitelyPresentable X n (D.obj i) (hstage i)⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
