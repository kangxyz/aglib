/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleDerivedFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompactificationAmplitude
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition

/-! # Original proper finite-presentation direct images on bounded constructibles

Quasi-compactness of the target supplies an actual relative fibre bound.
The target need not be Noetherian or have finite Krull dimension.
The original functor, objects, arrows and derived worlds are retained.
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

variable {X S : Scheme.{u}} [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

include n hn hΛ in
/-- Actual proper images remain bounded constructible on a quasi-compact target. -/
theorem moduleDerivedDirectImage_proper_finitePresentation_boundedConstructible
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleBoundedConstructibleCohomologyPlus X Λ K) :
    moduleBoundedConstructibleCohomologyPlus S Λ
      ((moduleDerivedDirectImage Λ f).obj K) := by
  refine ⟨moduleDerivedDirectImage_proper_finitePresentation_isConstructible
    f Λ n hn hΛ K hK.1, ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hK.2
  let : K.IsGE a := ha
  let C : Hom.Compactification f :=
    { Xbar := X
      j := 𝟙 X
      p := f
      isOpenImmersion_j := inferInstance
      isProper_p := inferInstance
      fac := Category.id_comp f }
  obtain ⟨d, hd⟩ := exists_moduleCompactification_upperAmplitude C Λ n hn
    (by simpa using hΛ)
  refine ⟨a, (d : ℤ) + b,
    (moduleDirectImage f Λ).rightDerivedFunctorPlus_isGE K a, ?_⟩
  let : ((moduleDerivedDirectImage Λ C.p).obj
      ((moduleDerivedLowerShriek C.j Λ).obj K)).IsLE ((d : ℤ) + b) := hd K a b ha hb
  let e := (moduleDerivedDirectImage Λ f).mapIso
    ((moduleDerivedLowerShriekIdIso Λ X).app K)
  exact DerivedCategory.Plus.TStructure.t.isLE_of_iso e _

/-- The original proper direct image on the original bounded constructible objects. -/
def moduleProperFinitePresentationBoundedConstructible :
    (moduleBoundedConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleBoundedConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleBoundedConstructibleCohomologyPlus S Λ)
    ((moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f)
    (fun K => moduleDerivedDirectImage_proper_finitePresentation_boundedConstructible
      f Λ n hn hΛ K.obj K.property)

/-- Forgetting output bounds and constructibility gives the unchanged original functor. -/
def moduleProperFinitePresentationBoundedConstructibleForgetIso :
    moduleProperFinitePresentationBoundedConstructible f Λ n hn hΛ ⋙
        (moduleBoundedConstructibleCohomologyPlus S Λ).ι ≅
      (moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
