/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.TorsionConstructible
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.WeakSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactInverseImage

/-! # General-ring exceptional images of internally torsion constructible D+

The original compactification functor preserves constructible homology on
native bounded-below complexes whose individual homology sheaves are internally
torsion. Finite Postnikov propagation requires no common annihilator.
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

/-- A supplied actual compactification preserves constructible homology on all
native bounded-below internally torsion complexes, by original finite Postnikov layers. -/
theorem moduleCompactificationHomology_torsion_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hKt : moduleTorsionCohomologyPlus X Λ K)
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
    let M := (DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K
    let V := (moduleSheafEquivalence X Λ).inverse.obj M
    have hVt : Sheaf.IsTorsion ((Constructible.Modules.moduleUnderlying Λ X).obj V) :=
      (hKt i).of_iso ((moduleSheafInverseUnderlyingIso X Λ).app M)
    have hsingle := (moduleCompactificationSingleHomology_isConstructible_iff C Λ
      ((moduleSheafEquivalence X Λ).functor.obj V)).mpr
        (fun q => moduleCompactificationHigherImage_torsion_isConstructible
          f Λ V (hK i) hVt C q)
    exact (Constructible.Modules.isConstructible_iff_of_iso
      ((moduleSheafEquivalence S Λ).inverse.mapIso
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (k - i)).mapIso
          (F.mapIso ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).mapIso
            ((moduleSheafEquivalence X Λ).counitIso.app M)))))).mp (hsingle (k - i))

/-- The unchanged chosen exceptional functor preserves constructible homology
on the original internally torsion bounded-below range over any Noetherian ring. -/
theorem moduleExceptionalHomology_torsion_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)
    (hK : ∀ i : ℤ, Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K.obj))) (n : ℤ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) n).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj K))) :=
  moduleCompactificationHomology_torsion_isConstructible
    (moduleExceptionalCompactification f).toCompactification Λ K.obj K.property hK n

end AlgebraicGeometry.Scheme.EtaleCohomology
