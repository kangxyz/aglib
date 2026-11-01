/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LeftUnitSourceExpansion
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitSource
public import Aglib.CategoryTheory.Functor.IdentitySourceRestriction

/-! # Original torsion-source restriction of the left-unit contraction -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y}
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The actual source contraction, including the torsion inclusion unitor. -/
abbrev moduleLeftUnitRestrictedContraction :=
  Functor.isoWhiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (moduleDerivedIdentityFactorizationIso Λ X hX hX) ≪≫
    Functor.rightUnitor (@moduleTorsionCohomologyPlus X Λ _ hX).ι

/-- The original identity proper-image contraction inside the source. -/
abbrev moduleLeftUnitRestrictedImageIdentity :=
  Functor.isoWhiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (Functor.isoWhiskerLeft (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (@moduleDerivedDirectImageIdIso Λ _ X hX) ≪≫
      Functor.rightUnitor (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))

/-- The proved source-expansion equality is retained as a whole equation under inclusion. -/
theorem moduleLeftUnitRestrictedExpansion :
    Functor.isoWhiskerRight (moduleLeftUnitRestrictedContraction Λ hX)
        (@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      Functor.isoWhiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
        (moduleLeftUnitTargetExpansion C Λ hX hD) =
    Functor.isoWhiskerRight (moduleLeftUnitRestrictedImageIdentity Λ hX)
      (@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) :=
  identitySourceExpansion_whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (moduleDerivedIdentityFactorizationIso Λ X hX hX)
    (Functor.isoWhiskerLeft (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
      (@moduleDerivedDirectImageIdIso Λ _ X hX) ≪≫
      Functor.rightUnitor (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))
    (moduleLeftUnitTargetExpansion C Λ hX hD)
    (moduleLeftUnitSourceExpansion_normalize C Λ hX hD)

variable [QuasiCompact f]
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))

/-- This is the original first-refinement map, not a map chosen from the unit law. -/
abbrev moduleLeftUnitRestrictedFirstComparison :=
  Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (CategoryTheory.imageComparison
      (@moduleDerivedRefinementComparison X X (𝟙 X) _
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX)
      (@moduleDerivedRefinementDirectImageIso Λ _ X X (𝟙 X) hX
        (Hom.CompactifiedComposition.leftUnit C).first
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (Hom.CompactifiedComposition.leftUnitFirstRefinement C) hA hX))

/-- Its normalization is inherited from the original proper compositor and original unit. -/
theorem moduleLeftUnitRestrictedFirstComparison_eq :
    moduleLeftUnitRestrictedFirstComparison C Λ hX hA =
      (moduleLeftUnitRestrictedImageIdentity Λ hX).hom ≫
        Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
          (@moduleDerivedRefinementComparison X X (𝟙 X) _
            (Hom.CompactifiedComposition.leftUnit C).first
            (Hom.DenseCompactification.ofProper (𝟙 X))
            (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX) := by
  apply NatTrans.ext
  funext K
  have h := congrArg (fun τ => τ.app K.obj)
    (moduleLeftUnitFirstComparison_identityTarget Λ C hX hA)
  let a := Functor.whiskerLeft (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
    (@moduleDerivedDirectImageIdIso Λ _ X hX).hom
  let b := (Functor.rightUnitor
    (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)).hom
  let δ := @moduleDerivedRefinementComparison X X (𝟙 X) _
    (Hom.CompactifiedComposition.leftUnit C).first
    (Hom.DenseCompactification.ofProper (𝟙 X))
    (Hom.CompactifiedComposition.leftUnitFirstRefinement C) Λ _ hX hA hX
  change _ = a.app K.obj ≫ b.app K.obj ≫ δ.app K.obj at h
  change _ = (a.app K.obj ≫ b.app K.obj) ≫ δ.app K.obj
  exact h.trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
