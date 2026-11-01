/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeDiagram

/-!
# Canonical arbitrary base change for the chosen bounded-below exceptional functor

The component at the chosen source compactification is the original normalized
model exchange. Its target is transported by the canonical cofiltered
comparison, not by a fresh arbitrary isomorphism. Compatibility with every
source and target compactification proves independence of both choices.
Compactifiability after pullback comes from the actual normalized pullback;
no qcqs assumption is imposed on the new base. Pasting of successive base
changes is a separate result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)

local instance : Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]

/-- The original normalized exchange, canonically transported to any specified target model. -/
def moduleCompactificationBaseChangeIsoTo
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f)) :
    moduleCompactificationFunctor f Λ C ⋙ moduleDerivedInverseImage Λ b ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleCompactificationFunctor (pullback.fst b f) Λ D :=
  moduleNormalizedCompactificationBaseChangeIso C b Λ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
      (moduleCompactificationComparison (pullback.fst b f) Λ
        (Hom.DenseCompactification.baseChangeObj b C) D)

/-- Canonical exceptional base change on native torsion input, with ambient D+ output. -/
def moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ⋙ moduleDerivedInverseImage Λ b ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleExceptionalDirectImagePlusOfNonempty (pullback.fst b f) Λ :=
  moduleCompactificationBaseChangeIsoTo f b Λ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst b f))

/-- Transport through any source and target compactifications computes the same
chosen base-change map. This is actual comparison independence, not an isomorphism choice. -/
theorem moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_model
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f)) :
    Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
        (moduleDerivedInverseImage Λ b) ≪≫ moduleCompactificationBaseChangeIsoTo f b Λ C D =
      moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ D) := by
  exact isoComparison_model_transport
    ((Functor.whiskeringLeft _ _ _).obj
      (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ))
    (moduleNormalizedCompactificationBaseChangeIso
      (moduleExceptionalSuppliedCompactification f) b Λ)
    (moduleNormalizedCompactificationBaseChangeIso C b Λ)
    (Functor.isoWhiskerRight
      (moduleCompactificationComparison f Λ (moduleExceptionalSuppliedCompactification f) C)
      (moduleDerivedInverseImage Λ b))
    (moduleCompactificationComparison (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleCompactificationComparison (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C) D)
    (moduleCompactificationComparison (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (moduleExceptionalSuppliedCompactification (pullback.fst b f)))
    (moduleCompactificationComparison (pullback.fst b f) Λ
      (moduleExceptionalSuppliedCompactification (pullback.fst b f)) D)
    (moduleCompactificationBaseChangeComparison f b Λ
      (moduleExceptionalSuppliedCompactification f) C)
    ((moduleCompactificationComparison_trans (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (Hom.DenseCompactification.baseChangeObj b C) D).trans
      (moduleCompactificationComparison_trans (pullback.fst b f) Λ
        (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
        (moduleExceptionalSuppliedCompactification (pullback.fst b f)) D).symm)

/-- The same canonical base-change isomorphism with native torsion targets on both sides. -/
def moduleExceptionalDirectImagePlusTorsionBaseChangeIsoOfNonempty :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
        moduleDerivedInverseImageTorsion b Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleExceptionalDirectImagePlusTorsionOfNonempty (pullback.fst b f) Λ :=
  (moduleTorsionCohomologyPlus T Λ).liftFunctorIso
    (moduleExceptionalDirectImagePlusOfNonempty f Λ ⋙ moduleDerivedInverseImage Λ b)
    (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
      moduleExceptionalDirectImagePlusOfNonempty (pullback.fst b f) Λ)
    (fun K => ((moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
      moduleDerivedInverseImageTorsion b Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
      moduleExceptionalDirectImagePlusTorsionOfNonempty (pullback.fst b f) Λ).obj K).property)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ)

/-- Restricting the target keeps the literal original chosen base-change hom. -/
theorem moduleExceptionalDirectImagePlusTorsionBaseChangeIsoOfNonempty_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleExceptionalDirectImagePlusTorsionBaseChangeIsoOfNonempty f b Λ).hom.app K).hom =
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
