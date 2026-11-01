/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChangeIdentity

/-! # Given-presentation identity normalization on native torsion output -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wS wL wX' wM wN wP wR
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (a : X' ⟶ X) (sq : IsPullback a f' f (𝟙 S))

variable [QuasiCompact f] [QuasiCompact f']
  [Nonempty (Hom.DenseCompactification f)] [Nonempty (Hom.DenseCompactification f')]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hL : HasDerivedCategory.{wL} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

local instance cartesianIdentityTorsionLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩


/-- The identical given-square identity normalization holds on native torsion
output, by faithful inclusion; no new cohomological assertion is required. -/
theorem moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty_identity :
    moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty f f' (𝟙 S) a sq Λ =
      identityFunctorNormalizer (moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ)
          (moduleDerivedInverseImageTorsionIdIso Λ S) ≪≫
        moduleExceptionalDirectImagePlusTorsionSourceIsoOfNonempty f f'
          (cartesianIdentitySourceIso f f' a sq) (cartesianIdentitySourceIso_fac f f' a sq) Λ ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (fun k : X' ⟶ X => moduleDerivedInverseImageTorsion k Λ)
            (cartesianIdentitySourceIso_hom f f' a sq)))
          (moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  have h := congrArg (fun i => i.hom.app K)
    (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_identity f f' a sq Λ)
  have hId (M : (moduleTorsionCohomologyPlus S Λ).FullSubcategory) :
      ((moduleDerivedInverseImageTorsionIdIso Λ S).hom.app M).hom =
        (moduleDerivedInverseImageIdIso Λ S).hom.app M.obj := by
    change (moduleDerivedInverseImageIdIso Λ S).hom.app M.obj ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hMap {M N : (moduleTorsionCohomologyPlus X' Λ).FullSubcategory} (t : M ⟶ N) :
      ((moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ).map t).hom =
        (moduleExceptionalDirectImagePlusOfNonempty f' Λ).map t := rfl
  simp only [identityFunctorNormalizer, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Functor.comp_obj,
    moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty_hom_app,
    moduleExceptionalDirectImagePlusTorsionSourceIsoOfNonempty_hom_app, hId, hMap] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
