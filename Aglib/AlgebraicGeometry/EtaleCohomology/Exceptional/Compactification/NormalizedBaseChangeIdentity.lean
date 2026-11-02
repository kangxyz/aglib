/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawIdentityBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange

/-!
# Actual normalized identity base change in the supplied common models

The base and the transported original ambient retain their original derived
models. The raw and normalized pullback ambients and the literal pullback
source have independent models. Transport to independently chosen copies of
the same base or ambient category is a separate native-model comparison step.
-/

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
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  [HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ)]

/-- Derived-category instance on module sheaves over `(C.toCompactification.baseChange (𝟙 S)).Xbar`,
using the instance on `(pullback (𝟙 S) C.p)`.
-/
local instance normalizedIdentityRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
/-- Derived-category instance on module sheaves over
`((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar`, using the instance on
`C.Xbar`.
-/
local instance normalizedIdentityTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(C.toCompactification.baseChange (𝟙 S))).Xbar`, using the instance on
`(Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar`.
-/
local instance normalizedIdentityDenseModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange (𝟙 S))).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ))

/-- Normalized identity base change is the original source transport followed
by the transition of the actual dense identity comparison. -/
theorem moduleNormalizedCompactificationBaseChangeIso_identity :
    NormalizedIdentityBaseChangeEquation
      (moduleNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ).hom
      (moduleDerivedInverseImageIdIso Λ S)
      (moduleRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
        (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
        C.toCompactification)
      (moduleRawCompactificationTransition
        (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
        ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom
        (Hom.DenseCompactification.isPullback_open
          (Hom.DenseCompactification.baseChangeIdentityIso f C).hom)
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac Λ) :=
  normalizedIdentityBaseChangeEquation
    (moduleRawCompactificationTransition C.toCompactification C.toCompactification
      (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
      (Category.id_comp C.p) Λ)
    (moduleRawCompactificationBaseChangeIso C.toCompactification (𝟙 S) Λ).hom
    (moduleRawSourceIsoBaseChangeMap (Hom.DenseCompactification.identitySourceIso f)
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification Λ)
    (moduleIdentityRawProjectionTransition C Λ)
    (moduleCompactificationDensificationMap (C.toCompactification.baseChange (𝟙 S)) Λ)
    _ (moduleNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ).hom
    (moduleDerivedInverseImageIdIso Λ S) _
    (moduleRawIdentityBaseChange_naturality C Λ)
    (moduleRawDenseIdentityTransition C Λ)
    (moduleRawSourceIsoBaseChangeMap_identity (Hom.DenseCompactification.identitySourceIso f)
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification Λ)
    (moduleIdentityNormalizationTransition C Λ)
    (moduleNormalizedCompactificationBaseChangeIso_hom C (𝟙 S) Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
