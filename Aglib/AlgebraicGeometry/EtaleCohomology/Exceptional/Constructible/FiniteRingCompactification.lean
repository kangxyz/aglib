/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperFiniteRing
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LowerShriek
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty

/-! # Arbitrary constructible finite-ring coefficients in actual compactifications

Actual extension by zero preserves finite-type module constructibility. The
proper finite-ring producer therefore applies to the literal extended coefficient,
without a Galois reduction or any assumption that a bounded torsion lift exists.
The original exact-single and homology comparisons give actual compactified
exceptional homology in every integer degree.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS wAM wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S}
    (C : Hom.Compactification f) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAM} (AbelianSheaf.{u, u + 1} C.Xbar)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The unchanged compactified higher image of any constructible finite-ring
coefficient is constructible. The original structural map need not be proper. -/
theorem moduleCompactificationHigherImage_finiteRing_isConstructible
    (q : ℕ) (M : ModuleSheaf X Λ)
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj M)) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj M)) := by
  let : IsLocallyNoetherian C.Xbar := LocallyOfFiniteType.isLocallyNoetherian C.p
  let : CompactSpace C.Xbar := QuasiCompact.compactSpace_of_compactSpace C.p
  let : IsNoetherian C.Xbar := ⟨⟩
  exact moduleHigherDirectImage_proper_finiteRing_isConstructible Λ C.p q
    ((moduleLowerShriek C.j Λ).obj M)
    (Constructible.Modules.isConstructible_moduleLowerShriek_of_isNoetherian C.j M hM)

variable [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Every integer homology object of the literal compactified derived image of
an original constructible single is constructible, including negative degrees.
This uses the original derived functors, not a postulated bounded-category lift. -/
theorem moduleCompactificationSingleHomology_finiteRing_isConstructible
    (i : ℤ) (M : ModuleSheaf X Λ)
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj M)) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) i).obj
          ((moduleDerivedDirectImage Λ C.p).obj
            ((moduleDerivedLowerShriek C.j Λ).obj
              ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj M))))) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  let e := ((moduleLowerShriek C.j Λ).rightDerivedFunctorPlusSingleIso 0).app M
  apply P.prop_of_iso
    (((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) i).mapIso
      ((moduleDerivedDirectImage Λ C.p).mapIso e)).symm)
  exact (moduleDirectImage C.p Λ).property_single_homology_of_rightDerived P
    ((moduleLowerShriek C.j Λ).obj M)
    (fun q => moduleCompactificationHigherImage_finiteRing_isConstructible C Λ q M hM) i

end AlgebraicGeometry.Scheme.EtaleCohomology
