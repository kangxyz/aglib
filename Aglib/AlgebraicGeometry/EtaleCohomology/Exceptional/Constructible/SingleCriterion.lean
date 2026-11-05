/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty

/-! # Constructibility of original compactified singles

All natural-degree compactified higher images are equivalent to all-integer
homology constructibility of the original compactified single. The exact
lower-shriek single comparison and original proper right-derived comparison
supply the maps. Negative degrees vanish by the native lower bound.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every integer homology object of the original compactified single is
constructible exactly when every original natural higher image is. No
annihilator, ring finiteness, or geometric producer is assumed here. -/
theorem moduleCompactificationSingleHomology_isConstructible_iff
    {X S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] (M : ModuleSheaf X Λ) :
    (∀ i : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) i).obj
          ((moduleDerivedDirectImage Λ C.p).obj
            ((moduleDerivedLowerShriek C.j Λ).obj
              ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj M)))))) ↔
    (∀ q : ℕ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj M))) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  constructor
  · intro h q
    exact P.prop_of_iso ((moduleCompactificationHigherDirectImageHomologyIso C Λ q).app M).symm
      (h q)
  · intro h i
    let e := ((moduleLowerShriek C.j Λ).rightDerivedFunctorPlusSingleIso 0).app M
    apply P.prop_of_iso
      (((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) i).mapIso
        ((moduleDerivedDirectImage Λ C.p).mapIso e)).symm)
    exact (moduleDirectImage C.p Λ).property_single_homology_of_rightDerived P
      ((moduleLowerShriek C.j Λ).obj M) h i

end AlgebraicGeometry.Scheme.EtaleCohomology
