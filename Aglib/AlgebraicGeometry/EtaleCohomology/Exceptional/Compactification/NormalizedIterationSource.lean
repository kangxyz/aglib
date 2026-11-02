/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedIteration
public import Aglib.CategoryTheory.NatTrans.NormalizedIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeIterationPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawSourceIsoNaturality

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

/-- Derived-category instance on module sheaves over `(pullback (c ≫ b) C.p)`, using the instance on
`(C.toCompactification.baseChange (c ≫ b)).Xbar`.
-/
local instance normalizedSourceSingleRawModel :
    HasDerivedCategory.{wRs} (ModuleSheaf (pullback (c ≫ b) C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))
/-- Derived-category instance on module sheaves over `(iterationSingleRawModel b c C).Xbar`, using
the instance on `(C.toCompactification.baseChange (c ≫ b)).Xbar`.
-/
local instance normalizedSourceSingleTransportRawModel :
    HasDerivedCategory.{wRs} (ModuleSheaf (iterationSingleRawModel b c C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRs}
    (ModuleSheaf (C.toCompactification.baseChange (c ≫ b)).Xbar Λ))
/-- Derived-category instance on module sheaves over `(baseChangeObj (c ≫ b) C).Xbar`, using the
instance on `((baseChange (c ≫ b)).obj C).Xbar`.
-/
local instance normalizedSourceSingleDenseModel :
    HasDerivedCategory.{wNs} (ModuleSheaf (baseChangeObj (c ≫ b) C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(C.toCompactification.baseChange (c ≫ b))).Xbar`, using the instance on `((baseChange (c ≫
b)).obj C).Xbar`.
-/
local instance normalizedSourceSingleDensificationModel :
    HasDerivedCategory.{wNs}
      (ModuleSheaf (Hom.Compactification.densify
        (C.toCompactification.baseChange (c ≫ b))).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `((baseChange (c ≫ b) ⋙ iteratedSourceTransport
b c).obj C).Xbar`, using the instance on `((baseChange (c ≫ b)).obj C).Xbar`.
-/
local instance normalizedSourceSingleTransportDenseModel :
    HasDerivedCategory.{wNs}
      (ModuleSheaf ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNs} (ModuleSheaf ((baseChange (c ≫ b)).obj C).Xbar Λ))

/-- Derived-category instance on module sheaves over `(pullback b C.p)`, using the instance on
`(C.toCompactification.baseChange b).Xbar`.
-/
local instance normalizedSourceFirstRawNativeModel :
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ))
/-- Derived-category instance on module sheaves over `(pullback c (C.toCompactification.baseChange
b).p)`, using the instance on `((C.toCompactification.baseChange b).baseChange c).Xbar`.
-/
local instance normalizedSourceSecondRawNativeModel :
    HasDerivedCategory.{wRi}
      (ModuleSheaf (pullback c (C.toCompactification.baseChange b).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRi}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ))
/-- Derived-category instance on module sheaves over `(pullback c ((baseChange b).obj C).p)`, using
the instance on `(((baseChange b).obj C).toCompactification.baseChange c).Xbar`.
-/
local instance normalizedSourceSecondNormalizedRawNativeModel :
    HasDerivedCategory.{wRN} (ModuleSheaf (pullback c ((baseChange b).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ))

/-- Derived-category instance on module sheaves over `(baseChangeObj b C).Xbar`, using the instance
on `((baseChange b).obj C).Xbar`.
-/
local instance normalizedSourceFirstDenseModel :
    HasDerivedCategory.{wN₁} (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(C.toCompactification.baseChange b)).Xbar`, using the instance on `((baseChange b).obj C).Xbar`.
-/
local instance normalizedSourceFirstDensificationModel :
    HasDerivedCategory.{wN₁}
      (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(baseChangeObj c ((baseChange b).obj
C)).Xbar`, using the instance on `((baseChange c).obj ((baseChange b).obj C)).Xbar`.
-/
local instance normalizedSourceSecondDenseModel :
    HasDerivedCategory.{wNi} (ModuleSheaf (baseChangeObj c ((baseChange b).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify (((baseChange
b).obj C).toCompactification.baseChange c)).Xbar`, using the instance on `((baseChange c).obj
((baseChange b).obj C)).Xbar`.
-/
local instance normalizedSourceSecondDensificationModel :
    HasDerivedCategory.{wNi} (ModuleSheaf (Hom.Compactification.densify
      (((baseChange b).obj C).toCompactification.baseChange c)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- Derived-category instance on module sheaves over `((baseChange b ⋙ baseChange c).obj C).Xbar`,
using the instance on `((baseChange c).obj ((baseChange b).obj C)).Xbar`.
-/
local instance normalizedSourceIteratedDenseModel :
    HasDerivedCategory.{wNi} (ModuleSheaf ((baseChange b ⋙ baseChange c).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wNi}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- The original normalization transition on the actual transported single source. -/
def moduleIterationTransportedSingleNormalizationMap :
    moduleRawCompactificationFunctor (iterationSingleRawModel b c C) Λ ⟶
      moduleRawCompactificationFunctor
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification Λ :=
  moduleRawCompactificationTransition
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
    (iterationSingleRawModel b c C) (baseChangeNormalization (c ≫ b) C)
    (isPullback_iterationSingleNormalization b c C)
    (baseChangeNormalization_fst (c ≫ b) C) Λ

/-- The original transition along the actual normalized iteration isomorphism. -/
def moduleNormalizedIterationTransition :
    moduleRawCompactificationFunctor
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification Λ ⟶
      moduleRawCompactificationFunctor
        ((baseChange b ⋙ baseChange c).obj C).toCompactification Λ :=
  moduleRawCompactificationTransition
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
theorem moduleIterationSingleNormalization_source_naturality :
    SourceIsoNaturalityEquation
      (moduleCompactificationDensificationMap (C.toCompactification.baseChange (c ≫ b)) Λ)
      (moduleIterationTransportedSingleNormalizationMap b c C Λ)
      (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        (C.toCompactification.baseChange (c ≫ b))) :=
  moduleRawCompactificationSourceIso_refinement_naturality
    (iteratedSourceIso (f := f) b c) (pullback.fst c (pullback.fst b f))
    (iteratedSourceIso_hom_fst b c) ((baseChange (c ≫ b)).obj C).toCompactification
    (C.toCompactification.baseChange (c ≫ b)) (baseChangeNormalization (c ≫ b) C)
    (Hom.Compactification.isPullback_densify (C.toCompactification.baseChange (c ≫ b)))
    (isPullback_iterationSingleNormalization b c C)
    (baseChangeNormalization_fst (c ≫ b) C) Λ

omit [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- The normalized iterated exchange is identified with the original one-step
normalized exchange by the native source compositor and the actual original
iteration transition. This is an equality of the specified maps. -/
theorem moduleNormalizedIterationCompositeMap_source_pasting :
    RefinedSourceIsoPastingEquation
      (moduleNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ).hom
      (moduleNormalizedIterationCompositeMap b c C Λ)
      (moduleRawIterationSourceIso b c Λ)
      (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleNormalizedIterationTransition b c C Λ) :=
  refinedSourceIsoPastingEquation_normalize
    (moduleRawCompactificationBaseChangeIso C.toCompactification (c ≫ b) Λ).hom
    (moduleRawIterationCompositeMap C.toCompactification b c Λ)
    (moduleRawIterationSourceIso b c Λ)
    (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      (C.toCompactification.baseChange (c ≫ b)))
    (moduleRawIterationAmbientTransition C b c Λ)
    (moduleCompactificationDensificationMap (C.toCompactification.baseChange (c ≫ b)) Λ)
    (moduleIterationTransportedSingleNormalizationMap b c C Λ)
    (moduleIterationFinalNormalizationMap b c C Λ)
    (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleNormalizedIterationTransition b c C Λ)
    (moduleNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ).hom
    (moduleNormalizedIterationCompositeMap b c C Λ)
    (moduleRawIterationCompositeMap_source_pasting C b c Λ)
    (moduleIterationSingleNormalization_source_naturality b c C Λ)
    ((moduleIterationFinalNormalizationMap_triangle b c C Λ).trans
      (moduleNormalizedBaseChangeIteration_transition b c C Λ).symm)
    (moduleNormalizedCompactificationBaseChangeIso_hom C (c ≫ b) Λ) rfl

/-- The two original normalized base-change steps equal the original single
step after the specified native source compositor and actual iteration transition.
No additional quasi-compactness condition on either new base is imposed. -/
theorem moduleNormalizedBaseChangeIteration_equation :
    OriginalNormalizedIterationEquation
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (moduleNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ).hom
      (moduleNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ).hom
      (moduleDerivedInverseImageCompIso Λ b c)
      (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f)))
      (moduleRawIterationSourceIso b c Λ)
      (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
        (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
        ((baseChange (c ≫ b)).obj C).toCompactification)
      (moduleNormalizedIterationTransition b c C Λ) :=
  originalNormalizedIterationEquation_of_pasting
    (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
    (moduleNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ).hom
    (moduleNormalizedCompactificationBaseChangeIso C (c ≫ b) Λ).hom
    (moduleNormalizedIterationCompositeMap b c C Λ)
    (moduleDerivedInverseImageCompIso Λ b c)
    (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
      (pullback.snd c (pullback.fst b f)))
    (moduleRawIterationSourceIso b c Λ)
    (moduleRawCompactificationSourceIso (iteratedSourceIso (f := f) b c) Λ
      (pullback.fst c (pullback.fst b f)) (iteratedSourceIso_hom_fst b c)
      ((baseChange (c ≫ b)).obj C).toCompactification)
    (moduleNormalizedIterationTransition b c C Λ)
    (moduleNormalizedBaseChangeIteration_pasting b c C Λ)
    (moduleNormalizedIterationCompositeMap_source_pasting b c C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
