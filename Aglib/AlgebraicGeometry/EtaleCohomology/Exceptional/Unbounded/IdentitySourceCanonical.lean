/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoRefinement

/-! # The original identity-specific source comparison is the canonical source comparison -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wS wX' wM wN wR
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]

/-- The derived-category instance in universe `wM` for `Λ`-module sheaves on `C.Xbar`.
-/
local instance unboundedIdentityCanonicalOriginal (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
/-- The derived-category instance in universe `wN` for `Λ`-module sheaves on `(baseChangeObj (𝟙 S)
    C).Xbar`.
-/
local instance unboundedIdentityCanonicalNormalized (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wN} (ModuleSheaf (baseChangeObj (𝟙 S) C).Xbar Λ) :=
  targetModels (baseChangeObj (𝟙 S) C)
/-- The derived-category instance in universe `wM` for `Λ`-module sheaves on
    `((identitySourceTransport f).obj C).Xbar`.
-/
local instance unboundedIdentityCanonicalTransported (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wM} (ModuleSheaf ((identitySourceTransport f).obj C).Xbar Λ) :=
  sourceModels C

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- At the actual normalized identity model, the canonical source comparison uses
exactly the original identity-normalization refinement map. -/
theorem moduleUnboundedIdentitySourceModelIso_eq_canonical (C : Hom.DenseCompactification f) :
    moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ =
      moduleUnboundedCompactificationSourceIsoTo f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ N hN hΛ C (baseChangeObj (𝟙 S) C) := by
  refine Eq.trans ?_ (moduleUnboundedCompactificationSourceIsoTo_refinement
    f (pullback.fst (𝟙 S) f) (identitySourceIso f) (identitySourceIso_hom_f f)
    Λ N hN hΛ C (baseChangeIdentityIso f C).hom).symm
  apply Iso.ext
  have ht : moduleUnboundedIdentityComparisonTransition C Λ =
      @moduleUnboundedCompactificationMixedTransition (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f)
        _ Λ _ hX' hS ((baseChange (𝟙 S)).obj C) ((identitySourceTransport f).obj C)
        (baseChangeIdentityIso f C).hom (targetModels ((baseChange (𝟙 S)).obj C))
        (sourceModels C) :=
    @moduleUnboundedRawDenseTransition_eq_mixed (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f)
      _ Λ _ hX' hS ((baseChange (𝟙 S)).obj C) ((identitySourceTransport f).obj C)
      (baseChangeIdentityIso f C).hom (targetModels ((baseChange (𝟙 S)).obj C))
      (sourceModels C)
  change (moduleUnboundedRawCompactificationSourceIso (identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (identitySourceIso_hom_f f) C.toCompactification).hom ≫
      Functor.whiskerLeft _ (moduleUnboundedIdentityComparisonTransition C Λ) = _
  exact congrArg (fun t =>
    (moduleUnboundedRawCompactificationSourceIso (identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (identitySourceIso_hom_f f) C.toCompactification).hom ≫
      Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f)) t) ht

variable [Nonempty (Hom.DenseCompactification f)]
local instance unboundedIdentitySourceCanonicalNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩
variable [rawModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

/-- The independently defined identity-specific source transport equals the actual
canonical source-isomorphism comparison, including its original refinement units. -/
theorem moduleExceptionalUnboundedIdentitySourceIsoOfNonempty_eq_canonical :
    moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ =
      moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ N hN hΛ := by
  let C := moduleExceptionalSuppliedCompactification f
  let D := baseChangeObj (𝟙 S) C
  have hs : moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D =
      moduleUnboundedCompactificationSourceIsoTo f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ N hN hΛ C D := by
    exact (identitySource_post_self (moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ)
      (moduleUnboundedCompactificationComparison (pullback.fst (𝟙 S) f) Λ N hN hΛ D D)
      (moduleUnboundedCompactificationComparison_self (pullback.fst (𝟙 S) f) Λ N hN hΛ D)).trans
      (moduleUnboundedIdentitySourceModelIso_eq_canonical f Λ N hN hΛ C)
  exact identitySource_compare
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (𝟙 S) f) Λ N hN hΛ D)
    _ _ _ _ (moduleExceptionalUnboundedIdentitySourceIsoOfNonempty_model f Λ N hN hΛ C D)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model f (pullback.fst (𝟙 S) f)
      (identitySourceIso f) (identitySourceIso_hom_f f) Λ N hN hΛ C D) hs

end AlgebraicGeometry.Scheme.EtaleCohomology
