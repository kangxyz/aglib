/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleOpenHigherImageConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.CompactOpen

/-! # Constructible compactified higher images of original constant modules

The structural morphism is not asserted proper. Its supplied actual
compactification is used, and the closed complement is constructed from the
vanishing ideal of the open complement. Proper constant-module finiteness and
the actual localization sequence produce the result, with the original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wM wS wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every actual compactification gives constructible original compactified
higher images of a finite-type constant module with a positive annihilator.
No properness of the original morphism is assumed. -/
theorem constantTorsionModuleCompactificationHigherImage_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  let I := IdealSheafData.vanishingIdeal C.j.opensRange.compl
  have hc : Set.range C.j = (Set.range I.subschemeι)ᶜ := by
    dsimp only [I]
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl (Set.range C.j)).symm
  let A := (moduleSheafEquivalence C.Xbar Λ).functor.obj
    ((constantSheaf C.Xbar.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let c : (moduleInverseImage C.j Λ).obj A ≅
      (moduleSheafEquivalence X Λ).functor.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    (moduleInverseImageTransportIso C.j Λ).app A ≪≫
      (moduleSheafEquivalence X Λ).functor.mapIso
        (((moduleValuedInverseImage C.j Λ).mapIso
          ((moduleSheafEquivalence C.Xbar Λ).unitIso.app
            ((constantSheaf C.Xbar.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).symm) ≪≫
          (Constructible.Modules.moduleInverseImageConstantIso Λ C.j).app M)
  let : HasDerivedCategory.{u + 2} (AbelianSheaf.{u, u + 1} C.Xbar) :=
    HasDerivedCategory.standard _
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} C.Xbar) := hasExtStandard C.Xbar
  let : ∀ V : S.Etale, HasExt.{u + 2}
      (Sheaf ((Scheme.smallEtaleTopology C.Xbar).over
        ((siteBaseChange C.p).obj V)) AddCommGrpCat.{u + 1}) :=
    fun _ => HasExt.standard _
  let : ∀ V : S.Etale, HasExt.{u + 2}
      (AbelianSheaf.{u, u + 1} (pullback V.hom C.p)) := fun _ => hasExtStandard _
  have h := constantTorsionModuleOpenHigherDirectImage_isConstructible.{u, u + 2, u + 2,
    u + 2, wM, wS, u + 2, wAS} C.p Λ C.j I.subschemeι hc n hn M hM q
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      (((moduleDirectImage C.p Λ).rightDerived q).mapIso
        ((moduleLowerShriek C.j Λ).mapIso c)))).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
