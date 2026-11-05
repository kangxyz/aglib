/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleBoundedFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ModuleDerivedPullbackConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.ModuleDerivedBaseChangeProperty

/-! # Actual proper images have bounded constructible quasi-compact restrictions

The target itself need not be quasi-compact. Every original quasi-compact
base restriction is bounded using its own genuine relative bound; no global
bound over a non-quasi-compact target is silently asserted.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wS'
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Each original quasi-compact base restriction of the proper image is bounded constructible. -/
theorem moduleDerivedDirectImage_baseChange_boundedConstructible
    {X S S' : Scheme.{u}} [CompactSpace S']
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] (g : S' ⟶ S)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf (Limits.pullback f g) Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleBoundedConstructibleCohomologyPlus X Λ K) :
    moduleBoundedConstructibleCohomologyPlus S' Λ
      ((moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj K)) := by
  let f' := Limits.pullback.snd f g
  let g' := Limits.pullback.fst f g
  let K' := (moduleDerivedInverseImage Λ g').obj K
  have hK' := moduleDerivedInverseImage_boundedConstructible g' Λ K hK
  have hF := moduleDerivedDirectImage_proper_finitePresentation_boundedConstructible
    f' Λ n hn hΛ K' hK'
  let P : ObjectProperty (DerivedCategory.Plus (ModuleSheaf S' Λ)) :=
    moduleBoundedConstructibleCohomologyPlus S' Λ
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => (moduleBoundedConstructibleCohomologyPlus_iff_of_iso S' Λ e).mp h }
  exact (Proper.properModuleDerivedBaseChange_property_iff Λ f f' g g'
    (IsPullback.of_hasPullback f g) n hn hΛ K P).mpr hF

end AlgebraicGeometry.Scheme.EtaleCohomology
