/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Identity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoRefinement

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

/-- Derived-category instance on module sheaves over `C.Xbar`, supplied by `sourceModels C`.
-/
local instance identityCanonicalOriginal (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
/-- Derived-category instance on module sheaves over `(baseChangeObj (𝟙 S) C).Xbar`, supplied by
`targetModels (baseChangeObj (𝟙 S) C)`.
-/
local instance identityCanonicalNormalized (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wN} (ModuleSheaf (baseChangeObj (𝟙 S) C).Xbar Λ) :=
  targetModels (baseChangeObj (𝟙 S) C)
/-- Derived-category instance on module sheaves over `((identitySourceTransport f).obj C).Xbar`,
supplied by `sourceModels C`.
-/
local instance identityCanonicalTransported (C : Hom.DenseCompactification f) :
    HasDerivedCategory.{wM} (ModuleSheaf ((identitySourceTransport f).obj C).Xbar Λ) :=
  sourceModels C

/-- At the actual normalized identity model, the canonical source comparison uses
exactly the original identity-normalization refinement map. -/
theorem moduleIdentitySourceModelIso_eq_canonical (C : Hom.DenseCompactification f) :
    moduleIdentitySourceModelIso C Λ =
      moduleCompactificationSourceIsoTo f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ C (baseChangeObj (𝟙 S) C) := by
  refine Eq.trans ?_ (moduleCompactificationSourceIsoTo_refinement
    f (pullback.fst (𝟙 S) f) (identitySourceIso f) (identitySourceIso_hom_f f)
    Λ C (baseChangeIdentityIso f C).hom).symm
  apply Iso.ext
  have ht : moduleIdentityComparisonTransition C Λ =
      @moduleCompactificationMixedTransition (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f)
        _ Λ _ hX' hS ((baseChange (𝟙 S)).obj C) ((identitySourceTransport f).obj C)
        (baseChangeIdentityIso f C).hom (targetModels ((baseChange (𝟙 S)).obj C))
        (sourceModels C) :=
    @moduleRawDenseTransition_eq_mixed (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f)
      _ Λ _ hX' hS ((baseChange (𝟙 S)).obj C) ((identitySourceTransport f).obj C)
      (baseChangeIdentityIso f C).hom (targetModels ((baseChange (𝟙 S)).obj C))
      (sourceModels C)
  change (moduleRawCompactificationSourceIso (identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (identitySourceIso_hom_f f) C.toCompactification).hom ≫
      Functor.whiskerLeft _ (moduleIdentityComparisonTransition C Λ) = _
  exact congrArg (fun t =>
    (moduleRawCompactificationSourceIso (identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (identitySourceIso_hom_f f) C.toCompactification).hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ) t) ht

variable [Nonempty (Hom.DenseCompactification f)]
local instance identitySourceCanonicalNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩
variable [rawModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

/-- The independently defined identity-specific source transport equals the actual
canonical source-isomorphism comparison, including its original refinement units. -/
theorem moduleExceptionalIdentitySourceIsoOfNonempty_eq_canonical :
    moduleExceptionalIdentitySourceIsoOfNonempty f Λ =
      moduleExceptionalDirectImagePlusSourceIsoOfNonempty f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ := by
  let C := moduleExceptionalSuppliedCompactification f
  let D := baseChangeObj (𝟙 S) C
  have hs : moduleIdentitySourceModelIsoTo f Λ C D =
      moduleCompactificationSourceIsoTo f (pullback.fst (𝟙 S) f)
        (identitySourceIso f) (identitySourceIso_hom_f f) Λ C D := by
    exact (identitySource_post_self (moduleIdentitySourceModelIso C Λ)
      (moduleCompactificationComparison (pullback.fst (𝟙 S) f) Λ D D)
      (moduleCompactificationComparison_self (pullback.fst (𝟙 S) f) Λ D)).trans
      (moduleIdentitySourceModelIso_eq_canonical f Λ C)
  exact identitySource_compare
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (𝟙 S) f) Λ D)
    _ _ _ _ (moduleExceptionalIdentitySourceIsoOfNonempty_model f Λ C D)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model f (pullback.fst (𝟙 S) f)
      (identitySourceIso f) (identitySourceIso_hom_f f) Λ C D) hs

end AlgebraicGeometry.Scheme.EtaleCohomology
