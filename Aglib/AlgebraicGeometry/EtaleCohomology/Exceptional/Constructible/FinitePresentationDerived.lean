/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.SingleCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperModuleFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.QuasiCompactLowerShriekLocal
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
native bounded-below complexes over the same positive-characteristic ring,
by original finite Postnikov layers. -/
theorem moduleCompactificationHomology_finitePresentation_isConstructible
    {X S : Scheme.{u}} {f : X ⟶ S}
    (C : Hom.Compactification f) [LocallyOfFinitePresentation C.p] [QuasiCompact C.j]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
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
    let M := (DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) i).obj K
    let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} C.Xbar)
    let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
    have hsingle := (moduleCompactificationSingleHomology_isConstructible_iff C Λ M).mpr
      (fun q => moduleHigherDirectImage_proper_finitePresentation_isConstructible
        C.p Λ N hN hΛ ((moduleLowerShriek C.j Λ).obj M)
        (Constructible.Modules.isConstructible_moduleLowerShriek_of_quasiCompact
          C.j Λ M (hK i)) q)
    exact hsingle (k - i)



end AlgebraicGeometry.Scheme.EtaleCohomology
