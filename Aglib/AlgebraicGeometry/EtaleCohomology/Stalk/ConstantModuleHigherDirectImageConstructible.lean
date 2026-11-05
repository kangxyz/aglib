/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleCohomologyConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleHigherDirectImage

/-! # Constructible native higher images of prime-killed constant modules

The original scalar-linear sheafification comparison transports constructibility
to the actual valued higher direct image. The same original coefficient
equivalence then gives the native ringed-module statement. As for native
module lower shriek, constructibility of a native module sheaf is expressed
on its original inverse-valued image, not its underlying abelian group.

The coefficient is finite-type over its original ring and killed by one
prime. Its underlying group need not be finite. No prime-power or general
finite-ring reduction is asserted. The source, slice and fibre Ext worlds
and all four derived-category worlds remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

open Coefficients

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The actual valued higher direct image of a finite-type prime-killed constant
module is constructible for its original coefficient-ring action. -/
theorem constantPrimeKilledModuleValuedHigherDirectImage_isConstructible
    (p : ℕ) [Fact p.Prime] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((constantModuleValuedHigherDirectImage f Λ q).obj M) :=
  (Constructible.Modules.isConstructible_iff_of_iso
    ((constantModuleCohomologyHigherDirectImageIso.{u, w, s, max (u + 1) e, wMX, wMS, wAX, wAS}
      f Λ q).app M)).mp
        (constantPrimeKilledModuleCohomologySheafification_isConstructible.{u, u + 1, w, s, e}
          f p Λ M hM q)

/-- The genuine native higher direct image has the same constructibility,
viewed through the original constant-ring coefficient equivalence. -/
theorem constantPrimeKilledModuleNativeHigherDirectImage_isConstructible
    (p : ℕ) [Fact p.Prime] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleSheafEquivalence X Λ).functor.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) :=
  (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleHigherDirectImageValuedComparison f Λ q).app
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).mpr
        (constantPrimeKilledModuleValuedHigherDirectImage_isConstructible.{u, w, s, e,
          wMX, wMS, wAX, wAS}
          f Λ p M hM q)

end AlgebraicGeometry.Scheme.EtaleCohomology
