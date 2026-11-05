/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.Localization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.EmptySource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage
public import Aglib.Algebra.Homology.DerivedCategory.HomologyObjectProperty

/-! # Closed source reduction through the original exceptional triangle

When the complementary open source is empty, its actual exceptional image
is zero. The existing localization gluing therefore gives constructibility
from the original closed composite image, without bounded nilpotence or a
replacement coefficient category.
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

/-- An empty complementary open removes the open finiteness premise from
actual exceptional localization. In particular this applies to a surjective
closed source restriction and its empty open complement. -/
theorem moduleExceptionalHomology_isConstructible_of_empty_open [IsEmpty U] :
    letI := hX
    ∀ K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory,
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
  intro K hZ
  apply moduleExceptionalHomology_isConstructible_of_localization f j i Λ hcomp K ?_ hZ
  intro n
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleValuedSheaf S Λ) := Constructible.Modules.IsConstructible
  exact P.prop_of_isZero ((moduleSheafEquivalence S Λ).inverse.map_isZero
    ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).map_isZero
      (moduleExceptional_isZero_of_empty (j ≫ f) Λ
        ((moduleDerivedInverseImageTorsion j Λ).obj K))))

end AlgebraicGeometry.Scheme.EtaleCohomology
