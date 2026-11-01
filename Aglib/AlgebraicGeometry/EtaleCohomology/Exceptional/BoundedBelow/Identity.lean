/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnits

/-! # The original exceptional identity through an independent middle model

The literal identity compactification is contracted using the original ordinary
identity maps and native derived composition. The ambient middle model is not
identified with the endpoint model. Compatibility with the binary exceptional
compositor remains a separate unit-coherence assertion.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wM

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [endpointModel : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The actual identity compactification contracts through its independent middle model. -/
def moduleIdentityCompactificationAmbientIso :
    @moduleCompactificationFunctor X X (𝟙 X) Λ _ endpointModel endpointModel
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (middleModels (Hom.DenseCompactification.ofProper (𝟙 X))) ≅
      (moduleTorsionCohomologyPlus X Λ).ι :=
  Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedIdentityFactorizationIso Λ X endpointModel
        (middleModels (Hom.DenseCompactification.ofProper (𝟙 X)))) ≪≫
    Functor.rightUnitor _

/-- The same original identity contraction in the native torsion subcategory. -/
def moduleIdentityCompactificationIso :
    @moduleCompactificationTorsionFunctor X X (𝟙 X) Λ _ endpointModel endpointModel
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (middleModels (Hom.DenseCompactification.ofProper (𝟙 X))) ≅
      𝟭 (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  NatIso.ofComponents (fun K => (moduleTorsionCohomologyPlus X Λ).isoMk
    ((moduleIdentityCompactificationAmbientIso X Λ).app K)) (by
      intro K K' a
      apply ObjectProperty.hom_ext
      exact (moduleIdentityCompactificationAmbientIso X Λ).hom.naturality a)

/-- The lift has exactly the original ambient identity component. -/
theorem moduleIdentityCompactificationIso_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleIdentityCompactificationIso X Λ).hom.app K).hom =
      (moduleIdentityCompactificationAmbientIso X Λ).hom.app K := rfl

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- The chosen exceptional identity uses its original canonical comparison to the
literal identity compactification, followed by the original derived contraction. -/
def moduleExceptionalIdentityIso :
    @moduleExceptionalDirectImagePlusTorsion X X (𝟙 X) _ Λ _ endpointModel endpointModel
        _ _ _ _ (middleModels (moduleExceptionalCompactification (𝟙 X))) ≅
      𝟭 (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  moduleExceptionalDirectImagePlusTorsionIso (𝟙 X) Λ
      (Hom.DenseCompactification.ofProper (𝟙 X)) ≪≫
    moduleIdentityCompactificationIso X Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
