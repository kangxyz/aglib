/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteRingSingle
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.WeakSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage

/-! # Original finite-ring exceptional images preserve constructible homology

The source torsion lift is constructed on the entire original native D+ using
the finite ring's additive annihilator. Weak-Serre finite Postnikov propagation
and lower-bound preservation then prove every output homology constructible.
This does not claim an upper bound or a bounded constructible-category lift.
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

/-- Actual inclusion of the whole original finite-ring D+ in its internally
torsion range. Only the property proof changes; all objects and arrows are the same. -/
def moduleFiniteRingTorsionFunctor (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  ObjectProperty.lift (moduleTorsionCohomologyPlus X Λ) (𝟭 _)
    (fun K => moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ
      (Nat.card Λ) Nat.card_pos card_nsmul_eq_zero' K.obj)

/-- A supplied actual compactification preserves constructible homology on all
native bounded-below finite-ring complexes, by original finite Postnikov layers. -/
theorem moduleCompactificationHomology_finiteRing_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wAM} (AbelianSheaf.{u, u + 1} C.Xbar)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : ∀ i : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K)))
    (n : ℤ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleDerivedDirectImage Λ C.p).obj ((moduleDerivedLowerShriek C.j Λ).obj K)))) := by
  let : (moduleSheafEquivalence S Λ).inverse.Additive :=
    ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_inverse_additive.{u + 1, u, u + 1, u + 1}
      S.smallEtaleTopology Λ
  let P : ObjectProperty (ModuleSheaf S Λ) := ObjectProperty.inverseImage
    (Constructible.Modules.IsConstructible : ObjectProperty (ModuleValuedSheaf S Λ))
    (moduleSheafEquivalence S Λ).inverse
  let F := moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p
  apply DerivedCategory.Plus.homologyProperty_obj_of_homology_singles_weakSerre F P ?_ K ?_ n
  · intro L a hL
    let : L.IsGE a := hL
    let : ((moduleDerivedLowerShriek C.j Λ).obj L).IsGE a :=
      (moduleLowerShriek C.j Λ).rightDerivedFunctorPlus_isGE L a
    exact (moduleDirectImage C.p Λ).rightDerivedFunctorPlus_isGE _ a
  · intro i k
    apply P.prop_of_iso
      (DerivedCategory.Plus.homologyObjSingleShiftIso F _ i k).symm
    exact moduleCompactificationSingleHomology_finiteRing_isConstructible C Λ (k - i)
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K) (hK i)

/-- The unchanged chosen exceptional functor preserves constructible homology
for every original bounded-below finite-ring complex with constructible homology.
The torsion source inclusion is the explicitly constructed original-object lift. -/
theorem moduleExceptionalHomology_finiteRing_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    [HasDerivedCategory.{wAM}
      (AbelianSheaf.{u, u + 1} (moduleExceptionalCompactification f).Xbar)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : ∀ i : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K))) (n : ℤ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj
            ((moduleFiniteRingTorsionFunctor X Λ).obj K)))) :=
  moduleCompactificationHomology_finiteRing_isConstructible
    (moduleExceptionalCompactification f).toCompactification Λ K hK n

end AlgebraicGeometry.Scheme.EtaleCohomology
