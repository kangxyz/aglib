/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleInjectiveRefinementDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CompositeZeroDetection

/-! # Removing a genuine finite coefficient change from an original zero

For an original genuine injective module coefficient, the finite surjective
replacement detector returns zero from zero of the actual geometric pullback.
The proof keeps the upstairs injective, its actual adjunct and its literal
coefficient map: that coefficient map sends the supplied zero to zero.

After any original target refinement, the canonical inverse-image composition
isomorphism identifies the coefficient needed by this same finite detector.
Thus zero along the original composite finite cover returns zero along the
original target refinement. No zero-producing neighborhood is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Coefficients

universe u eY eY' eU eU'

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Zero of the original geometric pullback detects the original class when
its coefficient is pulled from a genuine injective on the coefficient base.
The actual finite replacement is constructed and used internally. -/
theorem moduleInjective_eq_zero_of_finite_pullback_eq_zero
    {T' T Y' Y : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
    (f : T' ⟶ T) [IsFinite f] [Surjective f] (f' : Y' ⟶ Y)
    (b : Y ⟶ T) (b' : Y' ⟶ T') (h : IsPullback b' f' f b)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf T Λ) [Injective I]
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q)
    (hc : cohomologyPullback.{u, eY, eY'} (X := Y) (S := Y') f'
      ((inverseImage b).obj ((SheafOfModules.toSheaf (constantRing T Λ)).obj I))
      q c = 0) : c = 0 := by
  obtain ⟨J, hJ, a, hdetect⟩ :=
    exists_moduleInjective_finite_refinement_detector.{u, eY, eY'} f Λ I
  apply hdetect f' b b' h q c
  rw [hc, map_zero]

/-- A genuine finite coefficient change can be removed after any original
target refinement. The supplied zero is along `k ≫ u`; the conclusion is
zero of the same original class along `u`, with no change of target axis. -/
theorem moduleInjective_restriction_eq_zero_of_finite_composite_eq_zero
    {T' T Y U U' : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eU} (AbelianSheaf.{u, u + 1} U)]
    [HasExt.{eU'} (AbelianSheaf.{u, u + 1} U')]
    (f : T' ⟶ T) [IsFinite f] [Surjective f]
    (b : Y ⟶ T) (u : U ⟶ Y) (k : U' ⟶ U) (bU' : U' ⟶ T')
    (h : IsPullback bU' k f (u ≫ b))
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf T Λ) [Injective I]
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q)
    (hc : cohomologyPullback.{u, eY, eU'} (X := Y) (S := U') (k ≫ u)
      ((inverseImage b).obj ((SheafOfModules.toSheaf (constantRing T Λ)).obj I))
      q c = 0) :
    cohomologyPullback.{u, eY, eU} (X := Y) (S := U) u
      ((inverseImage b).obj ((SheafOfModules.toSheaf (constantRing T Λ)).obj I))
      q c = 0 := by
  refine restriction_zero_of_composite_zero_of_iso_detector u k
    ((inverseImage b).obj ((SheafOfModules.toSheaf (constantRing T Λ)).obj I))
    ((inverseImage (u ≫ b)).obj ((SheafOfModules.toSheaf (constantRing T Λ)).obj I))
    ((inverseImageComp b u).symm.app
      ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)) q c ?_ hc
  intro d hd
  exact moduleInjective_eq_zero_of_finite_pullback_eq_zero
    f k (u ≫ b) bU' h Λ I q d hd

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
