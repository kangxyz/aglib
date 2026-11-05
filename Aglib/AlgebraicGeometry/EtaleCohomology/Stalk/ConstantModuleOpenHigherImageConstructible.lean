/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleHigherDirectImageAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ModuleHigherImageLocalization

/-! # Constructible higher images of open extensions of constant modules

The original constant coefficient on the proper ambient scheme and its actual
closed restriction both have constructible native higher images. The original
localization sequence therefore produces the open-extension term. No open
higher-image constructibility premise is supplied.
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
  (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{max (u + 1) e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- A positive-torsion finite-type constant coefficient restricted to an open
of a proper scheme has constructible higher images after original lower shriek.
The complementary closed coefficient is produced by the original pullback
comparison and the proved proper constant-module theorem. -/
theorem constantTorsionModuleOpenHigherDirectImage_isConstructible
    {U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i] (hc : Set.range j = (Set.range i)ᶜ)
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleLowerShriek j Λ).obj ((moduleInverseImage j Λ).obj
            ((moduleSheafEquivalence X Λ).functor.obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))))) := by
  let C := (moduleSheafEquivalence X Λ).functor.obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  apply moduleLowerShriekNativeHigherDirectImage_isConstructible_of_localization
    f j i hc Λ C (fun k =>
      constantTorsionModuleNativeHigherDirectImage_isConstructible f Λ n hn M hM k) ?_ q
  let c : (moduleInverseImage i Λ).obj C ≅
      (moduleSheafEquivalence Z Λ).functor.obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    (moduleInverseImageTransportIso i Λ).app C ≪≫
      (moduleSheafEquivalence Z Λ).functor.mapIso
        (((moduleValuedInverseImage i Λ).mapIso
          ((moduleSheafEquivalence X Λ).unitIso.app
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).symm) ≪≫
          (Constructible.Modules.moduleInverseImageConstantIso Λ i).app M)
  let : HasDerivedCategory.{u + 2} (ModuleSheaf Z Λ) := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (AbelianSheaf.{u, u + 1} Z) := HasDerivedCategory.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z) := hasExtStandard Z
  let : ∀ V : S.Etale, HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology Z).over
        ((siteBaseChange (i ≫ f)).obj V)) AddCommGrpCat.{u + 1}) :=
    fun _ => HasExt.standard _
  let : ∀ V : S.Etale, HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (pullback V.hom (i ≫ f))) :=
    fun _ => hasExtStandard _
  intro k
  apply (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      (((moduleDirectImage (i ≫ f) Λ).rightDerived k).mapIso c))).mpr
  exact constantTorsionModuleNativeHigherDirectImage_isConstructible.{u, u + 2, u + 2,
    u + 2, u + 2, wMS, u + 2, wAS} (i ≫ f) Λ n hn M hM k

end AlgebraicGeometry.Scheme.EtaleCohomology
