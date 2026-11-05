/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleFinitePresentationAffine

/-! # Original proper module constructibility over arbitrary bases

Unverified final source consumer: no base Noetherianity, global quasi-compactness,
finite additive carrier, invertibility, or supplied coefficient model is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Every original higher direct image under a proper finitely presented
morphism is constructible for left-Noetherian Z/n-algebra coefficients. -/
theorem moduleHigherDirectImage_proper_finitePresentation_isConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj F)) := by
  intro U
  let : IsAffine U.1.toScheme := U.2
  let f' := pullback.snd f U.1.ι
  let p := pullback.fst f U.1.ι
  let := HasDerivedCategory.standard (ModuleSheaf (pullback f U.1.ι) Λ)
  let := HasDerivedCategory.standard (ModuleSheaf U.1.toScheme Λ)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (pullback f U.1.ι))
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} U.1.toScheme)
  have hF' := moduleIsConstructible_inverseImage Λ p F hF
  have hG := moduleHigherDirectImage_proper_finitePresentation_isConstructible_of_isAffine
    f' Λ n hn hΛ ((moduleInverseImage p Λ).obj F) hF' q
  let P : ObjectProperty (ModuleSheaf U.1.toScheme Λ) := fun M =>
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence U.1.toScheme Λ).inverse.obj M)
  let : P.IsClosedUnderIsomorphisms := {
    of_iso := fun e h => (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence U.1.toScheme Λ).inverse.mapIso e)).mp h }
  have hU := (Proper.properModuleHigherBaseChange_property_iff
    Λ f f' U.1.ι p (IsPullback.of_hasPullback f U.1.ι) n hn hΛ q F P).mpr hG
  have hnative := (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleInverseImageValuedIso Λ U.1.ι).app
      (((moduleDirectImage f Λ).rightDerived q).obj F))).mp hU
  exact Constructible.Modules.nonempty_constructiblePartition hnative

end AlgebraicGeometry.Scheme.EtaleCohomology
