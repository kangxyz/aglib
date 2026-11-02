/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedIteration
public import Aglib.CategoryTheory.NatTrans.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChangeIterationPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoNaturality

/-!
# One-step identification of the original normalized iterated exchange

The actual raw source/ambient comparison is normalized using original
source-isomorphism naturality and the proved original normalization triangles.
The native source compositor and the actual target iteration transition remain
explicit. Source transport retains the supplied ambient derived model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Hom.DenseCompactification

universe u wX wS wM wX₁ wT wR₁ wN₁ wXi wU wRi wRN wNi wXs wRs wNs

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wXi} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wNi} (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ)]
  [HasDerivedCategory.{wXs} (ModuleSheaf (pullback (c ≫ b) f) Λ)]
  [HasDerivedCategory.{wRs} (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ)]
  [HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ)]

/-- The derived-category instance in universe `wRs` for `Λ`-module sheaves on `(pullback (c ≫ b)
    C.p)`.
-/
local instance unboundedNormalizedSourceSingleRawModel :
    HasDerivedCategory.{wRs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))
/-- The derived-category instance in universe `wRs` for `Λ`-module sheaves on
    `(iterationSingleRawModel b c C).Xbar`.
-/
local instance unboundedNormalizedSourceSingleTransportRawModel :
    HasDerivedCategory.{wRs} (ModuleSheaf (iterationSingleRawModel b c C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))
/-- The derived-category instance in universe `wNs` for `Λ`-module sheaves on `(baseChangeObj (c ≫
    b) C).Xbar`.
-/
local instance unboundedNormalizedSourceSingleDenseModel :
    HasDerivedCategory.{wNs} (ModuleSheaf (baseChangeObj (c ≫ b) C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))
/-- The derived-category instance in universe `wNs` for `Λ`-module sheaves on
    `(Hom.Compactification.densify (C.toCompactification.baseChange (c ≫ b))).Xbar`.
-/
local instance unboundedNormalizedSourceSingleDensificationModel :
    HasDerivedCategory.{wNs}
      (ModuleSheaf (Hom.Compactification.densify
        (C.toCompactification.baseChange (c ≫ b))).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))
/-- The derived-category instance in universe `wNs` for `Λ`-module sheaves on `((baseChange (c ≫ b)
    ⋙ iteratedSourceTransport b c).obj C).Xbar`.
-/
local instance unboundedNormalizedSourceSingleTransportDenseModel :
    HasDerivedCategory.{wNs}
      (ModuleSheaf ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))

/-- The derived-category instance in universe `wR₁` for `Λ`-module sheaves on `(pullback b C.p)`.
-/
local instance unboundedNormalizedSourceFirstRawNativeModel :
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ))
/-- The derived-category instance in universe `wRi` for `Λ`-module sheaves on `(pullback c
    (C.toCompactification.baseChange b).p)`.
-/
local instance unboundedNormalizedSourceSecondRawNativeModel :
    HasDerivedCategory.{wRi}
      (ModuleSheaf (pullback c (C.toCompactification.baseChange b).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ))
/-- The derived-category instance in universe `wRN` for `Λ`-module sheaves on `(pullback c
    ((baseChange b).obj C).p)`.
-/
local instance unboundedNormalizedSourceSecondNormalizedRawNativeModel :
    HasDerivedCategory.{wRN} (ModuleSheaf (pullback c ((baseChange b).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ))

/-- The derived-category instance in universe `wN₁` for `Λ`-module sheaves on `(baseChangeObj b
    C).Xbar`.
-/
local instance unboundedNormalizedSourceFirstDenseModel :
    HasDerivedCategory.{wN₁} (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- The derived-category instance in universe `wN₁` for `Λ`-module sheaves on
    `(Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar`.
-/
local instance unboundedNormalizedSourceFirstDensificationModel :
    HasDerivedCategory.{wN₁}
      (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- The derived-category instance in universe `wNi` for `Λ`-module sheaves on `(baseChangeObj c
    ((baseChange b).obj C)).Xbar`.
-/
local instance unboundedNormalizedSourceSecondDenseModel :
    HasDerivedCategory.{wNi} (ModuleSheaf (baseChangeObj c ((baseChange b).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))
/-- The derived-category instance in universe `wNi` for `Λ`-module sheaves on
    `(Hom.Compactification.densify (((baseChange b).obj C).toCompactification.baseChange c)).Xbar`.
-/
local instance unboundedNormalizedSourceSecondDensificationModel :
    HasDerivedCategory.{wNi} (ModuleSheaf (Hom.Compactification.densify
      (((baseChange b).obj C).toCompactification.baseChange c)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- The derived-category instance in universe `wNi` for `Λ`-module sheaves on `((baseChange b ⋙
    baseChange c).obj C).Xbar`.
-/
local instance unboundedNormalizedSourceIteratedDenseModel :
    HasDerivedCategory.{wNi} (ModuleSheaf ((baseChange b ⋙ baseChange c).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- The original normalization transition on the actual transported single source. -/
def moduleUnboundedIterationTransportedSingleNormalizationMap :
    moduleUnboundedRawCompactificationFunctor (iterationSingleRawModel b c C) Λ ⟶
      moduleUnboundedRawCompactificationFunctor
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification Λ :=
  moduleUnboundedRawCompactificationTransition
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
    (iterationSingleRawModel b c C) (baseChangeNormalization (c ≫ b) C)
    (isPullback_iterationSingleNormalization b c C)
    (baseChangeNormalization_fst (c ≫ b) C) Λ

/-- The original transition along the actual normalized iteration isomorphism. -/
def moduleUnboundedNormalizedIterationTransition :
    moduleUnboundedRawCompactificationFunctor
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification Λ ⟶
      moduleUnboundedRawCompactificationFunctor
        ((baseChange b ⋙ baseChange c).obj C).toCompactification Λ :=
  moduleUnboundedRawCompactificationTransition
    ((baseChange b ⋙ baseChange c).obj C).toCompactification
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
    (baseChangeIterationIso b c C).hom.hom
    (isPullback_open (baseChangeIterationIso b c C).hom)
    (baseChangeIterationIso b c C).hom.base_fac Λ

omit [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wNi} (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ)] in
/-- Actual source transport is natural for the original single densification map. -/
theorem moduleUnboundedIterationSingleNormalization_source_naturality :
    SourceIsoNaturalityEquation
      (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange (c ≫ b)) Λ)
      (moduleUnboundedIterationTransportedSingleNormalizationMap b c C Λ)
      (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        (C.toCompactification.baseChange (c ≫ b))) :=
  moduleUnboundedRawCompactificationSourceIso_refinement_naturality
    (iteratedSourceIso (f := f) b c) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso_hom_fst b c) ((baseChange (c ≫ b)).obj C).toCompactification
    (C.toCompactification.baseChange (c ≫ b)) (baseChangeNormalization (c ≫ b) C)
    (Hom.Compactification.isPullback_densify (C.toCompactification.baseChange (c ≫ b)))
    (isPullback_iterationSingleNormalization b c C)
    (baseChangeNormalization_fst (c ≫ b) C) Λ

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- The normalized iterated exchange is identified with the original one-step
normalized exchange by the native source compositor and the actual original
iteration transition. This is an equality of the specified maps. -/
theorem moduleUnboundedNormalizedIterationCompositeMap_source_pasting :
    RefinedSourceIsoPastingEquation
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ N hN hΛ).hom
      (moduleUnboundedNormalizedIterationCompositeMap b c C Λ)
      (moduleUnboundedRawIterationSourceIso b c Λ)
      (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleUnboundedNormalizedIterationTransition b c C Λ) :=
  refinedSourceIsoPastingEquation_normalize
    (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification (c ≫ b) Λ N hN hΛ).hom
    (moduleUnboundedRawIterationCompositeMap C.toCompactification b c Λ)
    (moduleUnboundedRawIterationSourceIso b c Λ)
    (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      (C.toCompactification.baseChange (c ≫ b)))
    (moduleUnboundedRawIterationAmbientTransition C b c Λ)
    (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange (c ≫ b)) Λ)
    (moduleUnboundedIterationTransportedSingleNormalizationMap b c C Λ)
    (moduleUnboundedIterationFinalNormalizationMap b c C Λ)
    (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleUnboundedNormalizedIterationTransition b c C Λ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ N hN hΛ).hom
    (moduleUnboundedNormalizedIterationCompositeMap b c C Λ)
    (moduleUnboundedRawIterationCompositeMap_source_pasting C b c Λ N hN hΛ)
    (moduleUnboundedIterationSingleNormalization_source_naturality b c C Λ)
    ((moduleUnboundedIterationFinalNormalizationMap_triangle b c C Λ).trans
      (moduleUnboundedNormalizedBaseChangeIteration_transition b c C Λ).symm)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom C (c ≫ b) Λ N hN hΛ) rfl

/-- The two original normalized base-change steps equal the original single
step after the specified native source compositor and actual iteration transition.
No additional quasi-compactness condition on either new base is imposed. -/
theorem moduleUnboundedNormalizedBaseChangeIteration_equation :
    OriginalNormalizedIterationEquation
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso
          ((baseChange b).obj C) c Λ N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ N hN hΛ).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ b c)
      (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f)))
      (moduleUnboundedRawIterationSourceIso b c Λ)
      (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleUnboundedNormalizedIterationTransition b c C Λ) :=
  originalNormalizedIterationEquation_of_pasting
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
    (moduleUnboundedNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ N hN hΛ).hom
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ N hN hΛ).hom
    (moduleUnboundedNormalizedIterationCompositeMap b c C Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b c)
    (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
      (pullback.snd c (pullback.fst b f)))
    (moduleUnboundedRawIterationSourceIso b c Λ)
    (moduleUnboundedRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleUnboundedNormalizedIterationTransition b c C Λ)
    (moduleUnboundedNormalizedBaseChangeIteration_pasting b c C Λ N hN hΛ)
    (moduleUnboundedNormalizedIterationCompositeMap_source_pasting b c C Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
