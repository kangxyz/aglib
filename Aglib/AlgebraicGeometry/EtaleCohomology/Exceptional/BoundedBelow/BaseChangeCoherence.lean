/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChange
public import Aglib.CategoryTheory.NatTrans.IdentityFunctorNormalizer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.IdentitySourceModel

/-!
# Chosen identity base change in a common base model

The identity-specific source transport is defined from the original source
isomorphism, original mixed-model refinement unit, and canonical target
comparison, never from base change. Its model independence follows from the
proved original identity normalization and original base-change model equation.
Source and target compactification-model families remain independent. Only the
base derived model is common; independently chosen copies of that same base
require the separate canonical native-model transport.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wX' wM wN wR
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
local instance : Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]

/-- Identity-specific source transport to a specified target model, defined
from original geometry and original unit comparisons rather than base change. -/
def moduleIdentitySourceModelIsoTo
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleCompactificationFunctor f Λ C ≅
      moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ ⋙
        moduleCompactificationFunctor (pullback.fst (𝟙 S) f) Λ D :=
  moduleIdentitySourceModelIso C Λ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ)
      (moduleCompactificationComparison (pullback.fst (𝟙 S) f) Λ
        (Hom.DenseCompactification.baseChangeObj (𝟙 S) C) D)

/-- Identity-specific chosen source transport, with no base-change map in its definition. -/
def moduleExceptionalIdentitySourceIsoOfNonempty :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ ⋙
        moduleExceptionalDirectImagePlusOfNonempty (pullback.fst (𝟙 S) f) Λ :=
  moduleIdentitySourceModelIsoTo f Λ (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S) f))

variable [rawModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

omit [Nonempty (Hom.DenseCompactification f)] in
/-- The actual original identity normalization at any two supplied models. -/
theorem moduleCompactificationBaseChangeIsoTo_identity
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleCompactificationBaseChangeIsoTo f (𝟙 S) Λ C D =
      identityFunctorNormalizer (moduleCompactificationFunctor f Λ C)
        (moduleDerivedInverseImageIdIso Λ S) ≪≫ moduleIdentitySourceModelIsoTo f Λ C D :=
  identityBaseChange_postcomp
    (moduleNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ)
    (moduleDerivedInverseImageIdIso Λ S) (moduleIdentitySourceModelIso C Λ)
    (moduleCompactificationComparison (pullback.fst (𝟙 S) f) Λ
      (Hom.DenseCompactification.baseChangeObj (𝟙 S) C) D)
    (moduleNormalizedBaseChange_identity_sourceModel C Λ)

/-- Chosen identity base change has the original identity normalization. -/
theorem moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_identity :
    moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f (𝟙 S) Λ =
      identityFunctorNormalizer (moduleExceptionalDirectImagePlusOfNonempty f Λ)
        (moduleDerivedInverseImageIdIso Λ S) ≪≫
      moduleExceptionalIdentitySourceIsoOfNonempty f Λ :=
  moduleCompactificationBaseChangeIsoTo_identity f Λ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S) f))

/-- The separately defined identity-specific source transport is independent
of the supplied source and target compactifications through original comparisons. -/
theorem moduleExceptionalIdentitySourceIsoOfNonempty_model
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C ≪≫
        moduleIdentitySourceModelIsoTo f Λ C D =
      moduleExceptionalIdentitySourceIsoOfNonempty f Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd (𝟙 S) f) Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (𝟙 S) f) Λ D) :=
  identitySourceTransport_model
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f (𝟙 S) Λ)
    (moduleCompactificationBaseChangeIsoTo f (𝟙 S) Λ C D)
    (moduleExceptionalIdentitySourceIsoOfNonempty f Λ) (moduleIdentitySourceModelIsoTo f Λ C D)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst (𝟙 S) f) Λ D)
    (moduleDerivedInverseImageIdIso Λ S)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_model f (𝟙 S) Λ C D)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_identity f Λ)
    (moduleCompactificationBaseChangeIsoTo_identity f Λ C D)

end AlgebraicGeometry.Scheme.EtaleCohomology
