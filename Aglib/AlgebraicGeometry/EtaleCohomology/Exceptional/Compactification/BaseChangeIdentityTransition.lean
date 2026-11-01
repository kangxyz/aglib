/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.IdentityRawProjection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawIdentityComparison

/-! # Original transition triangles for normalized identity base change -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wR wN
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original raw transition at the identity of a dense model is the identity. -/
theorem moduleRawDenseIdentityTransition :
    moduleRawCompactificationTransition C.toCompactification C.toCompactification
      (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
      (Category.id_comp C.p) Λ = 𝟙 (moduleRawCompactificationFunctor C.toCompactification Λ) := by
  have hi := moduleRawImageComparison_id C.j
    (Hom.DenseCompactification.isPullback_open (𝟙 C)) Λ C.p
  simpa only [moduleRawCompactificationTransition, moduleRawCompactificationFunctor,
    Functor.whiskerLeft_id'] using
    congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι) hi

variable [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  [HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ)]

local instance identityRawModel :
    HasDerivedCategory.{wR} (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
local instance identityTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance identityDenseModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange (𝟙 S))).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ))

omit [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] in
/-- Raw identity projection followed by original densification is exactly the
transition of the actual dense identity comparison. -/
theorem moduleIdentityNormalizationTransition :
    moduleRawCompactificationTransition
        (C.toCompactification.baseChange (𝟙 S))
        ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
        (pullback.snd (𝟙 S) C.p)
        (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
        (Hom.DenseCompactification.identityRawProjection_p C) Λ ≫
      moduleCompactificationDensificationMap (C.toCompactification.baseChange (𝟙 S)) Λ =
    moduleRawCompactificationTransition
      (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
      ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom
      (Hom.DenseCompactification.isPullback_open
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom)
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac Λ := by
  let n : (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar ⟶
      pullback (𝟙 S) C.p := Hom.DenseCompactification.baseChangeNormalization (𝟙 S) C
  have hn : n ≫ pullback.snd (𝟙 S) C.p =
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom :=
    (Hom.DenseCompactification.baseChangeIdentityIso_hom f C).symm
  have sq : IsPullback (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).j
      (𝟙 (pullback (𝟙 S) f)) (n ≫ pullback.snd (𝟙 S) C.p)
      ((Hom.DenseCompactification.identitySourceTransport f).obj C).j := by
    rw [hn]
    exact Hom.DenseCompactification.isPullback_open
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom
  have hp : (n ≫ pullback.snd (𝟙 S) C.p) ≫ C.p =
      (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).p := by
    rw [hn]
    exact (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac
  have ht := moduleRawCompactificationTransition_comp
    (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
    (C.toCompactification.baseChange (𝟙 S)) n
    (Hom.Compactification.isPullback_densify (C.toCompactification.baseChange (𝟙 S)))
    (Hom.Compactification.densifyι_p (C.toCompactification.baseChange (𝟙 S))) Λ
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
    (pullback.snd (𝟙 S) C.p)
    (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (Hom.DenseCompactification.identityRawProjection_p C) sq hp
  apply ht.symm.trans
  congr 1

end AlgebraicGeometry.Scheme.EtaleCohomology
