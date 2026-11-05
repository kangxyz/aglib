/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FinitePresentationFunctors
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ModuleDerivedPullbackConstructible

/-! # Original exceptional bounded constructibility locally on an arbitrary base

Every qcqs base restriction uses its original pullback map and chosen Rf!.
The source complex is the original inverse image. No global compactification,
Noetherian base or single bound over a non-quasi-compact target is assumed.
In particular every affine open of an arbitrary target supplies this statement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wT wX' wM
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Each original qcqs base restriction has bounded constructible exceptional
image, with its own genuine relative bound produced internally. -/
theorem moduleExceptional_finitePresentation_baseLocal_boundedConstructible
    {X S T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (g : T ⟶ S) (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf (pullback f g) Λ)]
    [HasDerivedCategory.{wM}
      (ModuleSheaf (moduleExceptionalCompactification (pullback.snd f g)).Xbar Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleBoundedConstructibleCohomologyPlus X Λ K) :
    moduleBoundedConstructibleCohomologyPlus T Λ
      ((moduleExceptionalDirectImagePlus (pullback.snd f g) Λ).obj
        ((modulePositiveCharacteristicTorsionFunctor (pullback f g) Λ N hN hΛ).obj
          ((moduleDerivedInverseImage Λ (pullback.fst f g)).obj K))) := by
  have h := moduleDerivedInverseImage_boundedConstructible (pullback.fst f g) Λ K hK
  exact (moduleExceptional_finitePresentation_boundedConstructible
    (pullback.snd f g) Λ N hN hΛ
    ((modulePositiveCharacteristicTorsionFunctor (pullback f g) Λ N hN hΛ).obj
      ((moduleDerivedInverseImage Λ (pullback.fst f g)).obj K)) h).2

end AlgebraicGeometry.Scheme.EtaleCohomology
