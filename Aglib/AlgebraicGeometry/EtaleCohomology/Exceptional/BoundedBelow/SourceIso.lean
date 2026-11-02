/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedDirectImage

/-! # Canonical exceptional source-isomorphism comparison with independent model families -/

@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wX' wS wM wN
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

/-- The target diagram retains the original invertible refinement maps. -/
instance moduleCompactificationSourceIsoTargetDiagram_map_isIso
    {C D : (Hom.DenseCompactification f')ᵒᵖ} (a : C ⟶ D) :
    IsIso ((moduleCompactificationSourceIsoTargetDiagram f' e Λ).map a) := by
  change IsIso (Functor.whiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
    ((moduleCompactificationDiagram (f := f') Λ).map a))
  infer_instance

/-- Actual source transport intertwines canonical comparisons of every pair of models. -/
theorem moduleCompactificationSourceIsoComparison (C D : Hom.DenseCompactification f) :
    moduleCompactificationSourceIsoModel f f' e he Λ C ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
          (moduleCompactificationComparison f' Λ
            ((Hom.DenseCompactification.sourceIso f' e he).obj C)
            ((Hom.DenseCompactification.sourceIso f' e he).obj D)) =
      moduleCompactificationComparison f Λ C D ≪≫
        moduleCompactificationSourceIsoModel f f' e he Λ D := by
  have hn := Functor.cofilteredComparison_natIso
    (Hom.DenseCompactification.sourceIso f' e he)
    (moduleCompactificationSourceIsoDiagram f f' e he Λ) C D
  dsimp only [moduleCompactificationSourceIsoTargetDiagram] at hn
  rw [← Functor.cofilteredComparison_postcomp] at hn
  exact hn

/-- Original source transport, then canonical comparison to any specified target model. -/
def moduleCompactificationSourceIsoTo
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification f') :
    moduleCompactificationFunctor f Λ C ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙ moduleCompactificationFunctor f' Λ D :=
  moduleCompactificationSourceIsoModel f f' e he Λ C ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
      (moduleCompactificationComparison f' Λ
        ((Hom.DenseCompactification.sourceIso f' e he).obj C) D)

variable [Nonempty (Hom.DenseCompactification f)]

include f e he in
omit [QuasiCompact f] [QuasiCompact f'] in
/-- Actual source transport supplies compactifiability of the new source. -/
theorem moduleSourceIsoTargetNonempty : Nonempty (Hom.DenseCompactification f') :=
  ⟨(Hom.DenseCompactification.sourceIso f' e he).obj
    (moduleExceptionalSuppliedCompactification f)⟩

variable [Nonempty (Hom.DenseCompactification f')]

/-- Canonical source-isomorphism comparison on ambient bounded-below output.
Only supplied compactifiability is used, not qcqs of the common base. -/
def moduleExceptionalDirectImagePlusSourceIsoOfNonempty :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleExceptionalDirectImagePlusOfNonempty f' Λ :=
  moduleCompactificationSourceIsoTo f f' e he Λ
    (moduleExceptionalSuppliedCompactification f) (moduleExceptionalSuppliedCompactification f')

/-- Every specified source and target compactification computes this same canonical map. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification f') :
    moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫
        moduleCompactificationSourceIsoTo f f' e he Λ C D =
      moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f' e he Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion e.hom Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso f' Λ D) :=
  isoComparison_model_transport
    ((Functor.whiskeringLeft _ _ _).obj (moduleDerivedInverseImageTorsion e.hom Λ))
    (moduleCompactificationSourceIsoModel f f' e he Λ
      (moduleExceptionalSuppliedCompactification f))
    (moduleCompactificationSourceIsoModel f f' e he Λ C)
    (moduleCompactificationComparison f Λ (moduleExceptionalSuppliedCompactification f) C)
    (moduleCompactificationComparison f' Λ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      ((Hom.DenseCompactification.sourceIso f' e he).obj C))
    (moduleCompactificationComparison f' Λ
      ((Hom.DenseCompactification.sourceIso f' e he).obj C) D)
    (moduleCompactificationComparison f' Λ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      (moduleExceptionalSuppliedCompactification f'))
    (moduleCompactificationComparison f' Λ (moduleExceptionalSuppliedCompactification f') D)
    (moduleCompactificationSourceIsoComparison f f' e he Λ
      (moduleExceptionalSuppliedCompactification f) C)
    ((moduleCompactificationComparison_trans f' Λ
      ((Hom.DenseCompactification.sourceIso f' e he).obj
        (moduleExceptionalSuppliedCompactification f))
      ((Hom.DenseCompactification.sourceIso f' e he).obj C) D).trans
      (moduleCompactificationComparison_trans f' Λ
        ((Hom.DenseCompactification.sourceIso f' e he).obj
          (moduleExceptionalSuppliedCompactification f))
        (moduleExceptionalSuppliedCompactification f') D).symm)

/-- The same canonical source comparison with the native torsion-valued target. -/
def moduleExceptionalDirectImagePlusTorsionSourceIsoOfNonempty :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ≅
      moduleDerivedInverseImageTorsion e.hom Λ ⋙
        moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ :=
  (moduleTorsionCohomologyPlus S Λ).liftFunctorIso
    (moduleExceptionalDirectImagePlusOfNonempty f Λ)
    (moduleDerivedInverseImageTorsion e.hom Λ ⋙
      moduleExceptionalDirectImagePlusOfNonempty f' Λ)
    (fun K => ((moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion e.hom Λ ⋙
      moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ).obj K).property)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f' e he Λ)

omit [QuasiCompact f] in
/-- Target restriction retains the identical original source-comparison component. -/
theorem moduleExceptionalDirectImagePlusTorsionSourceIsoOfNonempty_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleExceptionalDirectImagePlusTorsionSourceIsoOfNonempty f f' e he Λ).hom.app K).hom =
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f' e he Λ).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
