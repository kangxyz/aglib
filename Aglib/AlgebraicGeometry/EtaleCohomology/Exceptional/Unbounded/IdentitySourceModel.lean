/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawDenseTransition

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

/-- The derived-category instance in universe `wM` for `Λ`-module sheaves on
    `((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar`.
-/
local instance unboundedIdentitySourceAmbientModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The derived-category instance in universe `wN` for `Λ`-module sheaves on
    `((Hom.DenseCompactification.baseChange (𝟙 S)).obj C).Xbar`.
-/
local instance unboundedIdentityNormalizedFunctorModel : HasDerivedCategory.{wN}
    (ModuleSheaf ((Hom.DenseCompactification.baseChange (𝟙 S)).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ))

/-- The original unit transition of the actual identity comparison, retaining
the distinct original and normalized ambient models. -/
def moduleUnboundedIdentityComparisonTransition :=
  moduleUnboundedRawCompactificationTransition
    (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
    (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom
    (Hom.DenseCompactification.isPullback_open
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom)
    (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac Λ

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ in
omit [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] in
/-- The actual proper refinement transition is invertible over the torsion coefficient ring. -/
theorem moduleUnboundedIdentityComparisonTransition_isIso :
    IsIso (moduleUnboundedIdentityComparisonTransition C Λ) := by
  have ht : moduleUnboundedIdentityComparisonTransition C Λ =
      moduleUnboundedCompactificationMixedTransition Λ
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom :=
    moduleUnboundedRawDenseTransition_eq_mixed Λ
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom
  exact (congrArg (fun t => IsIso t) ht).mpr
    (moduleUnboundedCompactificationMixedTransition_isIso Λ
      (Hom.DenseCompactification.baseChangeIdentityIso f C).hom N hN hΛ)

/-- Identity-specific source transport, defined only from original source
transport and the original mixed-model refinement transition, without base change. -/
def moduleUnboundedIdentitySourceModelIso :
    moduleUnboundedRawCompactificationFunctor C.toCompactification Λ ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f) ⋙
        moduleUnboundedRawCompactificationFunctor
          (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification Λ := by
  exact moduleUnboundedRawCompactificationSourceIso
      (Hom.DenseCompactification.identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f))
      (@asIso _ _ _ _ (moduleUnboundedIdentityComparisonTransition C Λ)
        (moduleUnboundedIdentityComparisonTransition_isIso C Λ N hN hΛ))

variable [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

/-- The actual normalized base-change isomorphism has the original identity
normalization through the independently defined identity-specific source transport. -/
theorem moduleUnboundedNormalizedBaseChange_identity_sourceModel :
    moduleUnboundedNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ N hN hΛ =
      Functor.isoWhiskerLeft (moduleUnboundedRawCompactificationFunctor C.toCompactification Λ)
          (moduleUnboundedDerivedInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleUnboundedRawCompactificationFunctor C.toCompactification Λ) ≪≫
        moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ := by
  exact normalizedIdentityIso_of_equation
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ N hN hΛ)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification)
    (moduleUnboundedIdentityComparisonTransition C Λ)
    (moduleUnboundedIdentityComparisonTransition_isIso C Λ N hN hΛ)
    (moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ) rfl
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_identity C Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
