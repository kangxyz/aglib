/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianIdentity
public import Aglib.CategoryTheory.NatTrans.CartesianSourceIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.IdentitySourceCanonical
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoComposition

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

local instance unboundedCartesianIdentityLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Identity base change for the given square is the original identity normalizer
followed by the canonical comparison for its actual source isomorphism. The final
transport retains the equality with the original source arrow; no object is relabelled. -/
theorem moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_identity :
    CartesianSourceIdentityEquation
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty f f'
        (𝟙 S) a sq Λ N hN hΛ)
      (identityFunctorNormalizer (moduleExceptionalDirectImageUnboundedOfNonempty f Λ)
        (moduleUnboundedDerivedInverseImageIdIso Λ S))
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f'
        (cartesianIdentitySourceIso f f' a sq)
        (cartesianIdentitySourceIso_fac f f' a sq) Λ N hN hΛ)
      (eqToIso (congrArg (fun k : X' ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
        (cartesianIdentitySourceIso_hom f f' a sq))) := by
  have hβ := (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_identity f Λ N hN
      hΛ).trans
    (congrArg (fun s => identityFunctorNormalizer
      (moduleExceptionalDirectImageUnboundedOfNonempty f Λ)
      (moduleUnboundedDerivedInverseImageIdIso Λ S) ≪≫ s)
      (moduleExceptionalUnboundedIdentitySourceIsoOfNonempty_eq_canonical f Λ N hN hΛ))
  let n := identityFunctorNormalizer (moduleExceptionalDirectImageUnboundedOfNonempty f Λ)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
  let β := moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f (𝟙 S) Λ N hN hΛ
  let s₀ := moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f
    (pullback.fst (𝟙 S) f) (identitySourceIso f) (identitySourceIso_hom_f f) Λ N hN hΛ
  let s₁ := moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty
    (pullback.fst (𝟙 S) f) f' sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ
  let s := moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f'
    (cartesianIdentitySourceIso f f' a sq) (cartesianIdentitySourceIso_fac f f' a sq) Λ N hN hΛ
  let c := moduleUnboundedCartesianBaseChangeSourceIso f f' (𝟙 S) a sq Λ
  exact cartesianIdentity_forward_transport n β s₀ s₁ s c
    (moduleUnboundedDerivedInverseImageCompIso Λ (identitySourceIso f).hom sq.flip.isoPullback.hom)
    (eqToIso (congrArg (fun k : X' ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      (cartesianIdentitySourceIso_hom f f' a sq)))
    (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty f f'
      (𝟙 S) a sq Λ N hN hΛ) rfl hβ
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_composition
      f (pullback.fst (𝟙 S) f) f' (identitySourceIso f) sq.flip.isoPullback
      (identitySourceIso_hom_f f) sq.flip.isoPullback_hom_fst Λ N hN hΛ)
    (cartesianIdentity_eqToIso_symm_comp
      (fun k : X' ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
      (cartesianIdentitySourceIso_hom f f' a sq)
      (moduleUnboundedDerivedInverseImageCompIso Λ
        (identitySourceIso f).hom sq.flip.isoPullback.hom))

end AlgebraicGeometry.Scheme.EtaleCohomology
