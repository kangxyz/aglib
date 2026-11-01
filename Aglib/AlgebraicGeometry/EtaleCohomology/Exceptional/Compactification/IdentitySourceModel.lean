/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawDenseTransition

/-!
# Identity-source transport through the original mixed-model transition

This isomorphism is defined without base change: original source transport is
followed by the original invertible refinement unit for the actual dense
identity comparison. The original and normalized ambient models may differ.
The base derived model is common; no general same-scheme model identification
is implicit in this construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wN wR
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ)]

/-- Derived-category instance on module sheaves over
`((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar`, using the instance on
`C.Xbar`.
-/
local instance identitySourceAmbientModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- Derived-category instance on module sheaves over `((Hom.DenseCompactification.baseChange (𝟙
S)).obj C).Xbar`, using the instance on `(Hom.DenseCompactification.baseChangeObj (𝟙 S)
C).Xbar`.
-/
local instance identityNormalizedFunctorModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((Hom.DenseCompactification.baseChange (𝟙 S)).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ))

/-- The original unit transition of the actual identity comparison, retaining
the distinct original and normalized ambient models. -/
def moduleIdentityComparisonTransition :=
  moduleRawCompactificationTransition
    (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
    (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom
    (Hom.DenseCompactification.isPullback_open
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom)
    (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac Λ

omit [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] in
/-- Invertibility is supplied by the same original mixed-model refinement map. -/
instance moduleIdentityComparisonTransition_isIso :
    IsIso (moduleIdentityComparisonTransition C Λ) := by
  have ht : moduleIdentityComparisonTransition C Λ =
      moduleCompactificationMixedTransition Λ
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom :=
    moduleRawDenseTransition_eq_mixed Λ (Hom.DenseCompactification.baseChangeIdentityIso f C).hom
  rw [ht]
  exact moduleCompactificationMixedTransition_isIso Λ
    (Hom.DenseCompactification.baseChangeIdentityIso f C).hom

/-- Identity-specific source transport, defined only from original source
transport and the original mixed-model refinement transition, without base change. -/
def moduleIdentitySourceModelIso :
    moduleRawCompactificationFunctor C.toCompactification Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ ⋙
        moduleRawCompactificationFunctor
          (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification Λ := by
  exact moduleRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ)
      (@asIso _ _ _ _ (moduleIdentityComparisonTransition C Λ)
        (moduleIdentityComparisonTransition_isIso C Λ))

variable [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

/-- The actual normalized base-change isomorphism has the original identity
normalization through the independently defined identity-specific source transport. -/
theorem moduleNormalizedBaseChange_identity_sourceModel :
    moduleNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ =
      Functor.isoWhiskerLeft (moduleRawCompactificationFunctor C.toCompactification Λ)
          (moduleDerivedInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleRawCompactificationFunctor C.toCompactification Λ) ≪≫
        moduleIdentitySourceModelIso C Λ := by
  exact normalizedIdentityIso_of_equation
    (moduleNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ)
    (moduleDerivedInverseImageIdIso Λ S)
    (moduleRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification)
    (moduleIdentityComparisonTransition C Λ)
    (moduleIdentityComparisonTransition_isIso C Λ) (moduleIdentitySourceModelIso C Λ) rfl
    (moduleNormalizedCompactificationBaseChangeIso_identity C Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
