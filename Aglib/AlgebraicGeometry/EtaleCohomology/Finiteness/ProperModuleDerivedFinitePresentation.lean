/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.WeakSerre

/-! # Original proper finite-presentation direct images on constructible D+

Finite Postnikov propagation uses the genuine original higher-image theorem.
The base is arbitrary, and no uniform bound on input or output degrees is
asserted. The original functor, objects, arrows and derived worlds are retained.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wMX wMS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

include n hn hΛ in
/-- Original proper direct image preserves constructible homology over any base. -/
theorem moduleDerivedDirectImage_proper_finitePresentation_isConstructible
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleConstructibleCohomologyPlus X Λ K) :
    moduleConstructibleCohomologyPlus S Λ ((moduleDerivedDirectImage Λ f).obj K) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  intro k
  apply DerivedCategory.Plus.homologyProperty_obj_of_homology_singles_weakSerre
    (moduleDerivedDirectImage Λ f) P ?_ K ?_ k
  · intro L a hL
    let : L.IsGE a := hL
    exact (moduleDirectImage f Λ).rightDerivedFunctorPlus_isGE L a
  · intro i j
    apply P.prop_of_iso
      (DerivedCategory.Plus.homologyObjSingleShiftIso (moduleDerivedDirectImage Λ f) _ i j).symm
    exact (moduleDirectImage f Λ).property_single_homology_of_rightDerived P
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K)
      (fun q => moduleHigherDirectImage_proper_finitePresentation_isConstructible
        f Λ n hn hΛ _ (hK i) q) (j - i)

/-- The unchanged original proper functor on constructible bounded-below objects. -/
def moduleProperFinitePresentationConstructiblePlus :
    (moduleConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleConstructibleCohomologyPlus S Λ)
    ((moduleConstructibleCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f)
    (fun K => moduleDerivedDirectImage_proper_finitePresentation_isConstructible
      f Λ n hn hΛ K.obj K.property)

/-- Forgetting constructibility retains precisely the original functor and maps. -/
def moduleProperFinitePresentationConstructiblePlusForgetIso :
    moduleProperFinitePresentationConstructiblePlus f Λ n hn hΛ ⋙
        (moduleConstructibleCohomologyPlus S Λ).ι ≅
      (moduleConstructibleCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
