/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteRingComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ModuleCoefficientCoproducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # Proper constructibility with the original finite-ring coefficients

This is the thin consumer of the finite-ring constructibility equivalence and
the existing natural underlying comparison for the original higher direct image.
No preservation of injectives by scalar restriction is asserted or needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  Coefficients.hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

open Coefficients

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- Every original finite-ring module coefficient has constructible higher
images under a proper map to a Noetherian scheme, in every degree. -/
theorem moduleHigherDirectImage_proper_finiteRing_isConstructible
    (q : ℕ) (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj F)) := by
  have hA : Constructible.IsConstructible
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj F) :=
    (Constructible.isConstructible_iff_of_iso
      ((moduleSheafInverseUnderlyingIso X Λ).app F)).mp
        (Constructible.Modules.isConstructible_underlying hF)
  have hD := higherDirectImage_proper_isConstructible f q
    ((SheafOfModules.toSheaf (constantRing X Λ)).obj F) hA
  apply Constructible.Modules.isConstructible_of_finiteRingUnderlying
  exact (Constructible.isConstructible_iff_of_iso
    (((moduleSheafInverseUnderlyingIso S Λ).app
      (((moduleDirectImage f Λ).rightDerived q).obj F)) ≪≫
      ((moduleHigherDirectImageUnderlyingIso.{u, wMX, wMS, wAX, wAS} Λ f q).app F))).mpr hD

end AlgebraicGeometry.Scheme.EtaleCohomology
