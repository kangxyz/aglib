/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitRefinements
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.CategoryTheory.Adjunction.MateCounitEquation

/-! # The original counit face of the right-unit tower

The literal identity open has different endpoint and middle derived models.
The central square and its mixed mate are unchanged. This counit face is a
prerequisite for the normalized unit triangle, not that final triangle itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wY wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)

/-- The exact middle open in the supplied right-unit tower. -/
abbrev rightUnitMiddleOpen :
    (Hom.CompactifiedComposition.rightUnit C).first.Xbar ⟶ C.Xbar :=
  (Hom.CompactifiedComposition.rightUnit C).middleOpen

instance rightUnitMiddleOpen_isOpenImmersion : IsOpenImmersion (rightUnitMiddleOpen C) :=
  inferInstanceAs (IsOpenImmersion (Hom.CompactifiedComposition.rightUnit C).middleOpen)

variable (Λ : Type (u + 1)) [Ring Λ]
  (hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.rightUnit C).first.Xbar Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf Y Λ))

/-- The actual central exchange, retaining the independent identity-open model. -/
abbrev moduleRightUnitCentralMate :=
  @moduleProperOpenMate Λ _ Y (Hom.CompactifiedComposition.rightUnit C).first.Xbar
    Y C.Xbar (𝟙 Y) (rightUnitMiddleOpen C)
    (Hom.CompactifiedComposition.rightUnit C).first.p C.p _ _
    (Hom.CompactifiedComposition.rightUnit C).isPullback_middleOpen.flip hY hA hD hB

/-- The actual central mate has its original counit face, without replacing the
identity open by an identity functor or identifying either model on `Y`. -/
theorem moduleRightUnitCentralMate_counit :
    SpecifiedMateCounitEquation
      (@moduleDerivedAdjunction Y Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.p hY hA)
      (@moduleDerivedAdjunction Y Λ _ C.Xbar C.p hD hB)
      (TwoSquare.mk _ _ _ _
        (@moduleDerivedLowerShriekCartesianBaseChangeIso
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar Y C.Xbar Y
          (Hom.CompactifiedComposition.rightUnit C).first.p (rightUnitMiddleOpen C)
          (𝟙 Y) C.p _ _
          (Hom.CompactifiedComposition.rightUnit C).isPullback_middleOpen.flip
          Λ _ hA hY hB hD).hom)
      (moduleRightUnitCentralMate C Λ hY hA hB hD) :=
  specifiedMateCounitEquation _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
