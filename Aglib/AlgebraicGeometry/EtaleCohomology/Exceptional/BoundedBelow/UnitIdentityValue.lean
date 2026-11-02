/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Identity

/-! # The original identity contraction through one supplied middle model -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wM
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{wM} (ModuleSheaf X Λ))

/-- The original contraction, with source and middle native models specified independently. -/
def moduleSingleIdentityAmbientIso :
    (@moduleCompactificationValue X X (𝟙 X) Λ _ hX hX
      (Hom.DenseCompactification.ofProper (𝟙 X)) hM) ≅
      (@moduleTorsionCohomologyPlus X Λ _ hX).ι :=
  Functor.isoWhiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
    (moduleDerivedIdentityFactorizationIso Λ X hX hM) ≪≫
      Functor.rightUnitor (@moduleTorsionCohomologyPlus X Λ _ hX).ι

/-- Recording torsion properties does not change the original identity contraction. -/
def moduleSingleIdentityValueIso :
    (@moduleCompactificationSingleTorsionValue X X (𝟙 X) Λ _ hX hX
      (Hom.DenseCompactification.ofProper (𝟙 X)) hM) ≅
      𝟭 (@moduleTorsionCohomologyPlus X Λ _ hX).FullSubcategory :=
  NatIso.ofComponents (fun K => (@moduleTorsionCohomologyPlus X Λ _ hX).isoMk
    ((moduleSingleIdentityAmbientIso X Λ hX hM).app K)) (by
      intro K K' a
      apply ObjectProperty.hom_ext
      exact (moduleSingleIdentityAmbientIso X Λ hX hM).hom.naturality a)

/-- The actual underlying morphism is unchanged. -/
theorem moduleSingleIdentityValueIso_hom_app
    (K : (@moduleTorsionCohomologyPlus X Λ _ hX).FullSubcategory) :
    ((moduleSingleIdentityValueIso X Λ hX hM).hom.app K).hom =
      (moduleSingleIdentityAmbientIso X Λ hX hM).hom.app K := rfl

variable [models : ∀ C : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- At the original family model this is literally the original identity compactification iso. -/
theorem moduleSingleIdentityValueIso_original :
    moduleSingleIdentityValueIso X Λ hX (models (Hom.DenseCompactification.ofProper (𝟙 X))) =
      @moduleIdentityCompactificationIso X Λ _ hX models := rfl

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- The original chosen epsilon retains its original canonical comparison and contraction. -/
theorem moduleExceptionalIdentityIso_singleValue :
    @moduleExceptionalIdentityIso X Λ _ hX models _ _ =
      ((@moduleExceptionalDirectImagePlusTorsionIso X X (𝟙 X) _ Λ _ hX hX _ _ _ _ models
        (Hom.DenseCompactification.ofProper (𝟙 X)))) ≪≫
      moduleSingleIdentityValueIso X Λ hX
        (models (Hom.DenseCompactification.ofProper (𝟙 X))) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
