/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.NormalizationIteration
public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIteration
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawRefinementBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence

/-!
# Original normalization comparisons for consecutive base change

The actual native source associator identifies the source of the single raw
pullback with the iterated source. The actual closed ambient inclusion equation
then identifies the two original unit-induced normalization paths. This leaf
retains the geometric maps; their later combination with exchange pasting must
also retain the original source-transport comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u wX wU wI wN wR


namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Hom.DenseCompactification

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wI} (ModuleSheaf ((baseChange b ⋙ baseChange c).obj C).Xbar Λ)]
  [HasDerivedCategory.{wN}
    (ModuleSheaf ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).Xbar Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (iterationSingleRawModel b c C).Xbar Λ)]

/-- The two normalization routes induce the same original raw transition.
The equality is proved from actual comparison composition and the actual
ambient inclusion equation, not uniqueness of objectwise cohomology isomorphisms. -/
theorem moduleNormalizedBaseChangeIteration_transition :
    moduleRawCompactificationTransition
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
        (iterationSingleRawModel b c C) (baseChangeNormalization (c ≫ b) C)
        (isPullback_iterationSingleNormalization b c C)
        (baseChangeNormalization_fst (c ≫ b) C) Λ ≫
      moduleRawCompactificationTransition
        ((baseChange b ⋙ baseChange c).obj C).toCompactification
        ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
        (baseChangeIterationIso b c C).hom.hom
        (isPullback_open (baseChangeIterationIso b c C).hom)
        (baseChangeIterationIso b c C).hom.base_fac Λ =
    moduleRawCompactificationTransition
      ((baseChange b ⋙ baseChange c).obj C).toCompactification
      (iterationSingleRawModel b c C) (iteratedNormalization b c C)
      (isPullback_iteratedNormalization b c C) (iteratedNormalization_fst b c C) Λ := by
  have hs : IsPullback ((baseChange b ⋙ baseChange c).obj C).j
      (𝟙 (pullback c (pullback.fst b f)))
      ((baseChangeIterationIso b c C).hom.hom ≫ baseChangeNormalization (c ≫ b) C)
      (iterationSingleRawModel b c C).j := by
    rw [baseChangeIterationIso_hom_normalization]
    exact isPullback_iteratedNormalization b c C
  have hp : ((baseChangeIterationIso b c C).hom.hom ≫
      baseChangeNormalization (c ≫ b) C) ≫ (iterationSingleRawModel b c C).p =
      ((baseChange b ⋙ baseChange c).obj C).p := by
    rw [baseChangeIterationIso_hom_normalization]
    exact iteratedNormalization_fst b c C
  have hc := moduleRawCompactificationTransition_comp
    ((baseChange b ⋙ baseChange c).obj C).toCompactification
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).toCompactification
    (baseChangeIterationIso b c C).hom.hom
    (isPullback_open (baseChangeIterationIso b c C).hom)
    (baseChangeIterationIso b c C).hom.base_fac Λ
    (iterationSingleRawModel b c C) (baseChangeNormalization (c ≫ b) C)
    (isPullback_iterationSingleNormalization b c C)
    (baseChangeNormalization_fst (c ≫ b) C) hs hp
  rw [← hc]
  congr 1
  exact baseChangeIterationIso_hom_normalization b c C

end AlgebraicGeometry.Scheme.EtaleCohomology
