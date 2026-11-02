/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.NormalizedToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageOfNonempty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeModelEquation

/-! # Chosen arbitrary base change preserves the same canonical exceptional comparison -/
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

/-- The chosen original exchange commutes with the same canonical b, as computed through
any specified compactification and its actual raw-pullback normalization. -/
theorem moduleExceptionalToDirectImage_baseChange_model (C : Hom.DenseCompactification f) :
    ExchangeToTargetEquation (moduleExceptionalToDirectImageOfNonempty f Λ)
      (moduleExceptionalToDirectImageOfNonempty (pullback.fst b f) Λ)
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
          pullback.condition)) :=
  exchangeToTarget_transport
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalToDirectImageOfNonempty f Λ)
    (moduleExceptionalToDirectImageOfNonempty (pullback.fst b f) Λ)
    (moduleCompactificationToDirectImage f Λ C)
    (moduleCompactificationToDirectImage (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom
    (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition))
    (moduleExceptionalToDirectImageOfNonempty_model f Λ C)
    (moduleExceptionalToDirectImageOfNonempty_model (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalBaseChange_normalized_model f b Λ C)
    (moduleNormalizedCompactificationBaseChangeIso_toDirectImage C b Λ)
end AlgebraicGeometry.Scheme.EtaleCohomology
