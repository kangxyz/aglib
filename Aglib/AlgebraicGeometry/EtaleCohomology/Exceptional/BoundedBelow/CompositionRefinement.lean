/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModel
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionRestriction
public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare
public import Aglib.CategoryTheory.Adjunction.IdentitySourceMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison

/-! # Original squares for refinement of compactified composition towers

The middle-open refinement square is Cartesian by actual pullback pasting and
cancellation. It is the geometric input to the original compositor refinement
cube; the cube and choice independence are not consequences of this geometry
alone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition.Refinement

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} [QuasiCompact g]
  {C D : CompactifiedComposition f g} (a : Refinement C D)

/-- The intermediate opens of an actual tower refinement form an actual
Cartesian square, not just a commuting square. -/
theorem isPullback_middleOpen :
    IsPullback C.middleOpen a.intermediate.hom a.source.hom D.middleOpen := by
  have h := C.isPullback_middleOpen.paste_vert
    (DenseCompactification.isPullback_open a.target)
  have ht : IsPullback C.middleOpen
      (a.intermediate.hom ≫ D.first.p)
      (a.source.hom ≫ D.sourceCompactification.p) D.targetCompactification.j := by
    let hB : C.sourceCompactification.Xbar ⟶ D.sourceCompactification.Xbar := a.source.hom
    have hr : hB ≫ D.sourceCompactification.p =
        C.sourceCompactification.p ≫ a.target.hom := a.comm
    change IsPullback C.middleOpen (a.intermediate.hom ≫ D.first.p)
      (hB ≫ D.sourceCompactification.p) D.targetCompactification.j
    rw [a.intermediate.base_fac, hr]
    simpa only [Category.comp_id] using h
  exact ht.of_bot (intermediateMap_middleOpen a).symm D.isPullback_middleOpen

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition.Refinement

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe wX wC wD

section General

variable {X Y₁ Y₂ : Scheme.{u}} (j₁ : X ⟶ Y₁) (j₂ : X ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : Y₁ ⟶ Y₂)
  (sq : IsPullback j₁ (𝟙 X) h j₂) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf Y₂ Λ)]

/-- The actual refinement unit map is the original proper/open mixed mate,
normalized only by the original direct-image identity comparison. -/
theorem moduleDerivedProperRefinementComparison_identitySourceMate :
    IdentitySourceMateEquation
      (moduleDerivedAdjunction Λ (𝟙 X)) (moduleDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) j₁ j₂ h
          sq.flip Λ).hom)
      (moduleDerivedDirectImageIdIso Λ X)
      (moduleDerivedProperRefinementComparison j₁ j₂ h sq Λ) := by
  apply identitySourceMateEquation
    (moduleDerivedAdjunction Λ (𝟙 X)) (moduleDerivedAdjunction Λ h)
    (moduleDerivedInverseImageIdIso Λ X) (moduleDerivedDirectImageIdIso Λ X)
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ X)
    _ (moduleDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom _
  · intro K
    have hn := moduleDerivedLowerShriekCartesianBaseChangeIso_identity_source
      j₁ j₂ h sq.flip Λ
    have hp := congrArg (fun e => e.hom.app K) hn.symm
    change (moduleDerivedProperRefinementPullbackIso j₁ j₂ h sq Λ).hom.app K =
      (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) j₁ j₂ h
        sq.flip Λ).hom.app K ≫
      (moduleDerivedLowerShriek j₁ Λ).map
        ((moduleDerivedInverseImageIdIso Λ X).hom.app K) ≫ 𝟙 _ at hp
    rw [Category.comp_id] at hp
    exact hp
  · exact moduleDerivedProperRefinementComparison_app j₁ j₂ h sq Λ

end General

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The actual refinement unit map is the original proper/open mixed mate,
normalized only by the original direct-image identity comparison. -/
theorem moduleDerivedRefinementComparison_identitySourceMate :
    IdentitySourceMateEquation
      (moduleDerivedAdjunction Λ (𝟙 X)) (moduleDerivedAdjunction Λ a.hom)
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) C.j D.j a.hom
          (Hom.DenseCompactification.isPullback_open a).flip Λ).hom)
      (moduleDerivedDirectImageIdIso Λ X) (moduleDerivedRefinementComparison a Λ) :=
  moduleDerivedProperRefinementComparison_identitySourceMate C.j D.j a.hom
    (Hom.DenseCompactification.isPullback_open a) Λ

/-- Component form retains the exact original refinement and mixed-mate maps. -/
theorem moduleDerivedRefinementComparison_eq_mate_app
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedRefinementComparison a Λ).app K =
      (moduleDerivedLowerShriek D.j Λ).map
          ((moduleDerivedDirectImageIdIso Λ X).inv.app K) ≫
        (moduleProperOpenMate Λ D.j C.j (𝟙 X) a.hom
          (Hom.DenseCompactification.isPullback_open a).flip).app K :=
  (moduleDerivedRefinementComparison_identitySourceMate a Λ K).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
