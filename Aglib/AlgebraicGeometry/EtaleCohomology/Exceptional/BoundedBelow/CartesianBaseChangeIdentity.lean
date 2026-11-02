/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChange
public import Aglib.CategoryTheory.NatTrans.CartesianSourceIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.IdentitySourceCanonical
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoComposition

/-! # Identity normalization for an actual given Cartesian presentation -/

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

local instance cartesianIdentityLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

/-- Identity base change for the given square is the original identity normalizer
followed by the canonical comparison for its actual source isomorphism. The final
transport retains the equality with the original source arrow; no object is relabelled. -/
theorem moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_identity :
    moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f f' (𝟙 S) a sq Λ =
      identityFunctorNormalizer (moduleExceptionalDirectImagePlusOfNonempty f Λ)
          (moduleDerivedInverseImageIdIso Λ S) ≪≫
        moduleExceptionalDirectImagePlusSourceIsoOfNonempty f f'
          (cartesianIdentitySourceIso f f' a sq) (cartesianIdentitySourceIso_fac f f' a sq) Λ ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (fun k : X' ⟶ X => moduleDerivedInverseImageTorsion k Λ)
            (cartesianIdentitySourceIso_hom f f' a sq)))
          (moduleExceptionalDirectImagePlusOfNonempty f' Λ) := by
  have hβ := (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_identity f Λ).trans
    (congrArg (fun s => identityFunctorNormalizer
      (moduleExceptionalDirectImagePlusOfNonempty f Λ)
      (moduleDerivedInverseImageIdIso Λ S) ≪≫ s)
      (moduleExceptionalIdentitySourceIsoOfNonempty_eq_canonical f Λ))
  exact cartesianSourceExchange_identity _ _ _ _ _ _
    (moduleDerivedInverseImageTorsionCompIso Λ (identitySourceIso f).hom sq.flip.isoPullback.hom)
    (eqToIso (congrArg (fun k : X' ⟶ X => moduleDerivedInverseImageTorsion k Λ)
      (cartesianIdentitySourceIso_hom f f' a sq).symm)) hβ
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_composition
      f (pullback.fst (𝟙 S) f) f' (identitySourceIso f) sq.flip.isoPullback
      (identitySourceIso_hom_f f) sq.flip.isoPullback_hom_fst Λ) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
