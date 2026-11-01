/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Normalization
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeIteration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange

/-!
# Passing intermediate normalization through the next original base change

The first closed-densification comparison is moved through the second original
exchange using its proved raw-refinement naturality. The remaining comparison
is the actual pullback of that closed inclusion followed by the second original
densification. This is a route factorization, not yet the final chosen-functor
consecutive-base-change identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Hom.DenseCompactification

universe u wX₁ wT wR₁ wN₁ wX₂ wU wR₂ wRN wN₂ wRS

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]


variable
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf ((C.toCompactification.baseChange b)).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf (((baseChange b).obj C)).Xbar Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wR₂} (ModuleSheaf (((C.toCompactification.baseChange b).baseChange c)).Xbar
    Λ)]
  [HasDerivedCategory.{wRN} (ModuleSheaf ((((baseChange b).obj C).toCompactification.baseChange
    c)).Xbar Λ)]
  [HasDerivedCategory.{wN₂} (ModuleSheaf (((baseChange c).obj ((baseChange b).obj C))).Xbar Λ)]

local instance iterationComparisonRawNativeModel :
    HasDerivedCategory.{wR₂} (ModuleSheaf (pullback c ((C.toCompactification.baseChange b)).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₂} (ModuleSheaf (((C.toCompactification.baseChange
    b).baseChange c)).Xbar Λ))
local instance iterationComparisonNormalizedRawNativeModel :
    HasDerivedCategory.{wRN} (ModuleSheaf (pullback c (((baseChange b).obj C)).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN} (ModuleSheaf ((((baseChange b).obj
    C).toCompactification.baseChange c)).Xbar Λ))
local instance iterationComparisonFirstDensificationModel :
    HasDerivedCategory.{wN₁} (ModuleSheaf (Hom.Compactification.densify
      (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf (((baseChange b).obj C)).Xbar Λ))
local instance iterationComparisonSecondDensificationModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (Hom.Compactification.densify (((baseChange b).obj
      C).toCompactification.baseChange c)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂} (ModuleSheaf (((baseChange c).obj ((baseChange b).obj
    C))).Xbar Λ))

local instance iterationComparisonNextDenseModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (baseChangeObj c ((baseChange b).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))
local instance iterationComparisonDensifiedPullbackModel :
    HasDerivedCategory.{wRN}
      (ModuleSheaf (pullback c (Hom.Compactification.densify
        (C.toCompactification.baseChange b)).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN}
    (ModuleSheaf (pullback c ((baseChange b).obj C).p) Λ))

/-- The actual pulled-back first normalization, expressed by its original
unit-induced raw transition rather than a chosen ambient isomorphism. -/
def moduleIterationPulledNormalizationMap :
    moduleRawCompactificationFunctor ((C.toCompactification.baseChange b).baseChange c) Λ ⟶
      moduleRawCompactificationFunctor (((baseChange b).obj C).toCompactification.baseChange c) Λ
      :=
  moduleRawCompactificationTransition (((baseChange b).obj C).toCompactification.baseChange c)
    ((C.toCompactification.baseChange b).baseChange c)
    (Hom.Compactification.refinementBaseChangeMap (((baseChange b).obj C)).toCompactification
      (C.toCompactification.baseChange b)
      (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c)
    (Hom.Compactification.isPullback_refinementBaseChangeMap_open (((baseChange b).obj
      C)).toCompactification (C.toCompactification.baseChange b)
      (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c
      (Hom.Compactification.isPullback_densify (C.toCompactification.baseChange b)))
    (Hom.Compactification.refinementBaseChangeMap_fst (((baseChange b).obj C)).toCompactification
      (C.toCompactification.baseChange b)
      (baseChangeNormalization b C) (baseChangeNormalization_fst b C) c) Λ

/-- After sliding the first normalization, the remaining normalization consists
of its actual pulled-back transition followed by the second densification. -/
def moduleIterationFinalNormalizationMap :
    moduleRawCompactificationFunctor ((C.toCompactification.baseChange b).baseChange c) Λ ⟶
      moduleRawCompactificationFunctor (((baseChange c).obj ((baseChange b).obj
        C))).toCompactification Λ :=
  moduleIterationPulledNormalizationMap b c C Λ ≫ moduleCompactificationDensificationMap
    (((baseChange b).obj C).toCompactification.baseChange c) Λ

/-- The first actual normalization commutes with the next normalized exchange
through the original pulled-normalization and second-densification maps. -/
theorem moduleNormalizedBaseChangeIteration_intermediate :
    ExchangeNaturalityEquation (moduleCompactificationDensificationMap
      (C.toCompactification.baseChange b) Λ)
      (moduleNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ).hom
      (moduleRawCompactificationBaseChangeIso (C.toCompactification.baseChange b) c Λ).hom
      (moduleIterationFinalNormalizationMap b c C Λ) :=
  append_original_normalization _ _ _ _ _ _
    (moduleDensificationBaseChangeIso_naturality (C.toCompactification.baseChange b) c Λ)
    (moduleNormalizedCompactificationBaseChangeIso_hom ((baseChange b).obj C) c Λ)

omit [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ)] in
/-- The pulled-normalization transition uses exactly the pre-existing
iterated raw ambient map, not an isomorphic replacement. -/
theorem moduleIterationPulledNormalizationMap_eq :
    moduleIterationPulledNormalizationMap b c C Λ =
      moduleRawCompactificationTransition (((baseChange b).obj C).toCompactification.baseChange c)
        ((C.toCompactification.baseChange b).baseChange c) (iteratedRawMap b c C)
        (isPullback_iterationPulledNormalization b c C)
        (iteratedRawMap_fst b c C) Λ := by
  unfold moduleIterationPulledNormalizationMap
  congr 1

variable [HasDerivedCategory.{wRS} (ModuleSheaf (iterationSingleRawModel b c C).Xbar Λ)]

omit [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)] in
/-- The native ambient associator followed by the original pulled normalization
and second densification is exactly the original total normalization transition. -/
theorem moduleIterationFinalNormalizationMap_triangle :
    moduleRawCompactificationTransition ((C.toCompactification.baseChange b).baseChange c)
      (iterationSingleRawModel b c C)
        (iterationRawAmbientIso b c C).hom (isPullback_iterationRawAmbientIso b c C)
        (iterationRawAmbientIso_hom_p b c C) Λ ≫
      moduleIterationFinalNormalizationMap b c C Λ =
    moduleRawCompactificationTransition (((baseChange c).obj ((baseChange b).obj
      C))).toCompactification (iterationSingleRawModel b c C)
      (iteratedNormalization b c C) (isPullback_iteratedNormalization b c C)
      (iteratedNormalization_fst b c C) Λ := by
  let u := baseChangeNormalization c ((baseChange b).obj C)
  let v := iteratedRawMap b c C
  let w := (iterationRawAmbientIso b c C).hom
  have hs : IsPullback (((baseChange c).obj ((baseChange b).obj C))).j (𝟙 (pullback c
    (pullback.fst b f))) (u ≫ v) (((C.toCompactification.baseChange b).baseChange c)).j := by
    have hu : IsPullback ((baseChange c).obj ((baseChange b).obj C)).j
        (𝟙 (pullback c (pullback.fst b f))) u
        (((baseChange b).obj C).toCompactification.baseChange c).j :=
      Hom.Compactification.isPullback_densify
        (((baseChange b).obj C).toCompactification.baseChange c)
    have hv : IsPullback (((baseChange b).obj C).toCompactification.baseChange c).j
        (𝟙 (pullback c (pullback.fst b f))) v
        ((C.toCompactification.baseChange b).baseChange c).j :=
      isPullback_iterationPulledNormalization b c C
    simpa only [Category.id_comp] using hu.paste_vert hv
  have hp : (u ≫ v) ≫ (((C.toCompactification.baseChange b).baseChange c)).p = (((baseChange
    c).obj ((baseChange b).obj C))).p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => u ≫ z) (iteratedRawMap_fst b c C)).trans
        (baseChangeNormalization_fst c ((baseChange b).obj C)))
  have h₁ := moduleRawCompactificationTransition_comp (((baseChange c).obj ((baseChange b).obj
    C))).toCompactification (((baseChange b).obj C).toCompactification.baseChange c) u
    (Hom.Compactification.isPullback_densify (((baseChange b).obj C).toCompactification.baseChange
      c))
    (baseChangeNormalization_fst c ((baseChange b).obj C)) Λ ((C.toCompactification.baseChange
      b).baseChange c) v
    (isPullback_iterationPulledNormalization b c C) (iteratedRawMap_fst b c C) hs hp
  have hn : moduleIterationFinalNormalizationMap b c C Λ =
      moduleRawCompactificationTransition (((baseChange c).obj ((baseChange b).obj
        C))).toCompactification ((C.toCompactification.baseChange b).baseChange c) (u ≫ v) hs hp Λ
        :=
    (congrArg (fun t => t ≫ moduleCompactificationDensificationMap (((baseChange b).obj
      C).toCompactification.baseChange c) Λ)
      (moduleIterationPulledNormalizationMap_eq b c C Λ)).trans h₁.symm
  have he : (u ≫ v) ≫ w = iteratedNormalization b c C := Category.assoc _ _ _
  have hst : IsPullback (((baseChange c).obj ((baseChange b).obj C))).j (𝟙 (pullback c
    (pullback.fst b f)))
      ((u ≫ v) ≫ w) (iterationSingleRawModel b c C).j :=
    he.symm ▸ isPullback_iteratedNormalization b c C
  have hpt : ((u ≫ v) ≫ w) ≫ (iterationSingleRawModel b c C).p = (((baseChange c).obj ((baseChange
    b).obj C))).p :=
    he.symm ▸ iteratedNormalization_fst b c C
  have h₂ := moduleRawCompactificationTransition_comp (((baseChange c).obj ((baseChange b).obj
    C))).toCompactification ((C.toCompactification.baseChange b).baseChange c)
    (u ≫ v) hs hp Λ (iterationSingleRawModel b c C) w
    (isPullback_iterationRawAmbientIso b c C) (iterationRawAmbientIso_hom_p b c C) hst hpt
  have ht : moduleRawCompactificationTransition (((baseChange c).obj ((baseChange b).obj
    C))).toCompactification
      (iterationSingleRawModel b c C) ((u ≫ v) ≫ w) hst hpt Λ =
      moduleRawCompactificationTransition (((baseChange c).obj ((baseChange b).obj
        C))).toCompactification
        (iterationSingleRawModel b c C) (iteratedNormalization b c C)
        (isPullback_iteratedNormalization b c C) (iteratedNormalization_fst b c C) Λ := by
    congr 1
  exact (congrArg (fun t => moduleRawCompactificationTransition ((C.toCompactification.baseChange
    b).baseChange c)
    (iterationSingleRawModel b c C) w (isPullback_iterationRawAmbientIso b c C)
    (iterationRawAmbientIso_hom_p b c C) Λ ≫ t) hn).trans (h₂.symm.trans ht)

end AlgebraicGeometry.Scheme.EtaleCohomology
