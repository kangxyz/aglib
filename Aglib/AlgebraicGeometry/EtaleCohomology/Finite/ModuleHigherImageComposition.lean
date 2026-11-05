/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.RightDerived.Precomp
public import Aglib.Algebra.Homology.RightDerived.Postcomp
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Additive

/-! # Original higher-image composition with a finite first map

Finite direct image is exact and preserves injectives. Its actual image of the
chosen resolution supplies the natural-degree comparison. No second derived
category or alternate cohomology realization enters the construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {Y X S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (Λ : Type (u + 1)) [Ring Λ]

/-- The original native direct-image comparison at natural derived degree. -/
def finiteModuleHigherDirectImageCompIso [IsFinite g] (q : ℕ) :
    (moduleDirectImage (g ≫ f) Λ).rightDerived q ≅
      moduleDirectImage g Λ ⋙ (moduleDirectImage f Λ).rightDerived q :=
  Functor.rightDerivedNatIsoOfAdditive (moduleDirectImageCompIso Λ f g) q ≪≫
    Functor.rightDerivedPrecompIso (moduleDirectImage g Λ) (moduleDirectImage f Λ) q

/-- The same original direct-image transport on a valued coefficient; its
source unit is the actual unit of the fixed coefficient equivalence. -/
def moduleDirectImageValuedNativeObjIso (E : ModuleValuedSheaf Y Λ) :
    (moduleDirectImage g Λ).obj ((moduleSheafEquivalence Y Λ).functor.obj E) ≅
      (moduleSheafEquivalence X Λ).functor.obj ((moduleValuedDirectImage g Λ).obj E) :=
  (moduleDirectImageTransportIso g Λ).app ((moduleSheafEquivalence Y Λ).functor.obj E) ≪≫
    (moduleSheafEquivalence X Λ).functor.mapIso
      ((moduleValuedDirectImage g Λ).mapIso ((moduleSheafEquivalence Y Λ).unitIso.app E).symm)

/-- Finite composition in the original valued input and output conventions. -/
def finiteModuleHigherDirectImageValuedCompObjIso [IsFinite g]
    (E : ModuleValuedSheaf Y Λ) (q : ℕ) :
    (moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage (g ≫ f) Λ).rightDerived q).obj
          ((moduleSheafEquivalence Y Λ).functor.obj E)) ≅
      (moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj
          ((moduleSheafEquivalence X Λ).functor.obj ((moduleValuedDirectImage g Λ).obj E))) :=
  (moduleSheafEquivalence S Λ).inverse.mapIso
    (((finiteModuleHigherDirectImageCompIso f g Λ q).app
        ((moduleSheafEquivalence Y Λ).functor.obj E)) ≪≫
      ((moduleDirectImage f Λ).rightDerived q).mapIso
        (moduleDirectImageValuedNativeObjIso g Λ E))

end AlgebraicGeometry.Scheme.EtaleCohomology
