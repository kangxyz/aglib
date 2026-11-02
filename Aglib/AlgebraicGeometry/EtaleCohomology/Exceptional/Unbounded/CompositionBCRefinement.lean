/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBCNormalization
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

/-! # Original exchange under an actual over-base refinement

The structural and ambient maps retain their supplied names. Their original
triangle equations transport the preceding normalization to the exact native
over-base comparison used by raw compactification transitions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wM wS wU' wM' wN wT

variable {U M S U' M' N T : Scheme.{u}}
  (j : U ⟶ M) (p : M ⟶ S) (j' : U' ⟶ M') (p' : M' ⟶ T)
  (jN : U' ⟶ N) (pN : N ⟶ T) (h : N ⟶ M')
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion jN]
  (a : U' ⟶ U) (q : M' ⟶ M) (qN : N ⟶ M) (b : T ⟶ S)
  (hj : IsPullback a j' j q) (hp : p' ≫ b = q ≫ p)
  (sq : IsPullback jN (𝟙 U') h j') (hbase : h ≫ p' = pN) (hambient : h ≫ q = qN)
  (ht : IsPullback a jN j qN) (hpt : pN ≫ b = qN ≫ p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wM'} (ModuleSheaf M' Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf N Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

include hambient in
/-- Generalized exchange followed by an actual refinement uses exactly the
original over-base unit transition, with no replacement structural isomorphism. -/
theorem moduleUnboundedCompactifiedCommutingExchange_refinement_over :
    moduleUnboundedCompactifiedCommutingExchange j p jN pN a qN b ht hpt Λ =
      moduleUnboundedCompactifiedCommutingExchange j p j' p' a q b hj hp Λ ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ a)
          (imageComparison (moduleUnboundedDerivedProperRefinementComparison jN j' h sq Λ)
            (moduleUnboundedDerivedDirectImageOverIso Λ pN p' h hbase)) := by
  subst pN
  subst qN
  simpa only [moduleUnboundedDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl] using
    moduleUnboundedCompactifiedCommutingExchange_refinement j p j' p' jN h a q b hj hp sq ht hpt Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
