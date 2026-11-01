/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawSourceComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTargetIso
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition

/-! # Composition of actual raw source transports through the original ambient refinement -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX₀ wX₁ wX₂ wS wM
variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  [QuasiCompact f₂]
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂) (C : Hom.DenseCompactification f₀)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

local instance unboundedRawSourceCompositionFirstModel :
    HasDerivedCategory.{wM} (ModuleSheaf (rawSourceFirstModel f₀ f₁ e₁ h₁ C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance unboundedRawSourceCompositionSequentialModel : HasDerivedCategory.{wM}
    (ModuleSheaf (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance unboundedRawSourceCompositionCompositeModel : HasDerivedCategory.{wM}
    (ModuleSheaf (rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original identity-ambient refinement, not an identification of the two models. -/
def moduleUnboundedRawSourceCompositionTransition :=
  moduleUnboundedRawCompactificationTransition
    (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).toCompactification
    (rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).toCompactification
    (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.hom
    (isPullback_open (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom)
    (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.base_fac Λ

omit [QuasiCompact f₂] in
/-- The actual total open square, retaining the sequentially transported open immersion. -/
private theorem rawSourceCompositionOpen :
    IsPullback (e₂.hom ≫ e₁.hom)
      (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).j C.j (𝟙 C.Xbar) := by
  change IsPullback (e₂.hom ≫ e₁.hom) (e₂.hom ≫ e₁.hom ≫ C.j) C.j (𝟙 C.Xbar)
  exact IsPullback.of_horiz_isIso ⟨by
    simp only [Category.assoc, Category.comp_id]⟩

/-- The original source comparisons compose through the original identity-ambient
refinement and the original unbounded inverse-image compositor. -/
theorem moduleUnboundedRawCompactificationSourceIso_composition :
    SourceIsoCompositionEquation
      (moduleUnboundedRawCompactificationSourceIso e₁ Λ f₁ h₁ C.toCompactification)
      (moduleUnboundedRawCompactificationSourceIso e₂ Λ f₂ h₂
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C).toCompactification)
      (moduleUnboundedRawCompactificationSourceIso (e₂ ≪≫ e₁) Λ f₂
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) C.toCompactification)
      (moduleUnboundedRawSourceCompositionTransition f₀ f₁ f₂ e₁ e₂ h₁ h₂ C Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) := by
  let C₁ := rawSourceFirstModel f₀ f₁ e₁ h₁ C
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let C₀₂ := rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let hj := rawSourceCompositionOpen f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let : IsIso (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.hom :=
    inferInstanceAs (IsIso (𝟙 C.Xbar))
  have ht := moduleUnboundedRawSquareMap_targetIso C.toCompactification C₂.toCompactification
    C₀₂.toCompactification (e₂.hom ≫ e₁.hom) (𝟙 C.Xbar) (𝟙 C.Xbar) (𝟙 S)
    (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.hom
    (isPullback_open (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom)
    (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom.base_fac
    (Category.id_comp (𝟙 C.Xbar)) hj (isPullback_sourceIsoOpen (e₂ ≪≫ e₁) C.j)
    (isPullback_sourceIsoProperIdentity C.p) (isPullback_sourceIsoProperIdentity C.p) Λ
  have hp := moduleUnboundedRawSquareMap_sourceIso_pasting C.toCompactification
      C₁.toCompactification
    e₁.hom (𝟙 C.Xbar) (𝟙 S) e₂ f₂ h₂
    (isPullback_sourceIsoOpen e₁ C.j) (isPullback_sourceIsoProperIdentity C.p) hj Λ
  exact sourceIsoComposition_of_exchange
    (moduleUnboundedRawSourceIsoBaseChangeMap e₁ f₁ h₁ C.toCompactification Λ)
    (moduleUnboundedRawSourceIsoBaseChangeMap (e₂ ≪≫ e₁) f₂
      (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) C.toCompactification Λ)
    _ _ _ _ _ (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedRawSourceIsoBaseChangeMap_identity e₁ f₁ h₁ C.toCompactification Λ)
    (moduleUnboundedRawSourceIsoBaseChangeMap_identity (e₂ ≪≫ e₁) f₂
      (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) C.toCompactification Λ)
    (sourcePasting_target _ _ _ _ _ _ hp ht)

end AlgebraicGeometry.Scheme.EtaleCohomology
