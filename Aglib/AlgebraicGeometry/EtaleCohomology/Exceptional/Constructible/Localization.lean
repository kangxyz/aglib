/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.LocalizationComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage
public import Aglib.Algebra.Homology.DerivedCategory.HomologyObjectProperty

/-! # Constructibility through the original exceptional localization triangle

Open and closed exceptional images glue on the actual original coefficient.
Only the weak-Serre closure of constructible modules is used, not arbitrary
subobject closure or finite underlying abelian groups. All input, target and
compactification derived worlds are retained from the original compositor.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

universe u wU wZ wX wS wF wJ wI wJF wIF
variable {U Z X S : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
  [hU : HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [jModels : ∀ C : Hom.DenseCompactification j,
    HasDerivedCategory.{wJ} (ModuleSheaf C.Xbar Λ)]
  [iModels : ∀ C : Hom.DenseCompactification i,
    HasDerivedCategory.{wI} (ModuleSheaf C.Xbar Λ)]
  [jfModels : ∀ C : Hom.DenseCompactification (j ≫ f),
    HasDerivedCategory.{wJF} (ModuleSheaf C.Xbar Λ)]
  [ifModels : ∀ C : Hom.DenseCompactification (i ≫ f),
    HasDerivedCategory.{wIF} (ModuleSheaf C.Xbar Λ)]

variable (hcomp : Set.range j = (Set.range i)ᶜ)

include hcomp

/-- Original open and closed composite exceptional images with constructible
homology imply constructible homology of the original whole exceptional image.
The coefficient ring may be infinite; no coefficient annihilator is supplied
beyond the existing native torsion-cohomology input range. -/
theorem moduleExceptionalHomology_isConstructible_of_localization :
    letI := hX
    ∀ K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory,
      (∀ n : ℤ, Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
            ((moduleExceptionalDirectImagePlus (j ≫ f) Λ).obj
              ((moduleDerivedInverseImageTorsion j Λ).obj K))))) →
      (∀ n : ℤ, Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
            ((moduleExceptionalDirectImagePlus (i ≫ f) Λ).obj
              ((moduleDerivedInverseImageTorsion i Λ).obj K))))) →
      ∀ n : ℤ, Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence S Λ).inverse.obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
            ((moduleExceptionalDirectImagePlus f Λ).obj K))) := by
  let := hX
  intro K hU hZ n
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  let T := moduleExceptionalLocalizationTriangle f j i Λ hX hcomp K
  have hT := moduleExceptionalLocalizationTriangle_distinguished f j i Λ hX hcomp K
  exact P.homology_middle_of_distinguished (DerivedCategory.Plus.ι.mapTriangle.obj T)
    (DerivedCategory.Plus.ι.map_distinguished T hT) hU hZ n

end AlgebraicGeometry.Scheme.EtaleCohomology
