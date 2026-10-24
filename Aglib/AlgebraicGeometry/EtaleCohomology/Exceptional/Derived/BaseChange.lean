/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.NatTrans
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport

/-!
# Original bounded-below base change for genuine constant-ring modules

The exchange is the actual mate of the inverse-image square under the installed
module-derived adjunctions. Its unit equation retains the original underived
module exchange. Constructing this map does not assert proper base change or
invertibility on torsion coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The native module-derived square uses the original inverse-image comparisons. -/
def moduleDerivedInverseImageSquareIso :
    moduleDerivedInverseImage Λ g ⋙ moduleDerivedInverseImage Λ f' ≅
      moduleDerivedInverseImage Λ f ⋙ moduleDerivedInverseImage Λ g' :=
  (moduleDerivedInverseImageCompIso Λ g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleDerivedInverseImage Λ k) h) ≪≫
      moduleDerivedInverseImageCompIso Λ f g'

/-- The derived square retains the actual square of original module complexes. -/
theorem moduleDerivedInverseImageSquareIso_exactComparison
    (K : CochainComplex.Plus (ModuleSheaf S Λ)) :
    ExactComparisonSquareEquation (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
      (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom) K := by
  have hc := exactComparisonSquareEquation
    (moduleInverseImage f Λ) (moduleInverseImage g' Λ)
    (moduleInverseImage g Λ) (moduleInverseImage f' Λ)
    (moduleInverseImage (f' ≫ g) Λ) (moduleInverseImage (g' ≫ f) Λ)
    (moduleInverseImageCompIso Λ g f') (moduleInverseImageCompIso Λ f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage k Λ) h)) K
  simp only [Functor.rightDerivedFunctorPlusIso_eqToIso] at hc
  simpa only [moduleDerivedInverseImageSquareIso, moduleDerivedInverseImageCompIso,
    moduleInverseImageSquareIso] using hc

/-- The genuine module exchange is the original derived adjunction mate. -/
def moduleDerivedBaseChangeMap :
    moduleDerivedDirectImage Λ f ⋙ moduleDerivedInverseImage Λ g ⟶
      moduleDerivedInverseImage Λ g' ⋙ moduleDerivedDirectImage Λ f' :=
  (mateEquiv (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)).natTrans

/-- The actual component is given by the original derived unit and counit. -/
theorem moduleDerivedBaseChangeMap_app (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    MateComponentEquation (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
      (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom K :=
  mateComponentEquation (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f')
    (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom K

/-- The original adjoint equation characterizes the module exchange. -/
theorem eq_moduleDerivedBaseChangeMap_iff
    (β : moduleDerivedDirectImage Λ f ⋙ moduleDerivedInverseImage Λ g ⟶
      moduleDerivedInverseImage Λ g' ⋙ moduleDerivedDirectImage Λ f') :
    β = moduleDerivedBaseChangeMap Λ f f' g g' h ↔
      ∀ K : DerivedCategory.Plus (ModuleSheaf X Λ),
        (moduleDerivedInverseImage Λ f').map (β.app K) ≫
            (moduleDerivedAdjunction Λ f').counit.app
              ((moduleDerivedInverseImage Λ g').obj K) =
          (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom.app
              ((moduleDerivedDirectImage Λ f).obj K) ≫
            (moduleDerivedInverseImage Λ g').map ((moduleDerivedAdjunction Λ f).counit.app K) :=
  eq_mateEquiv_iff (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ f') _ β

/-- The installed module exchange retains the original complex-level exchange and units. -/
theorem moduleDerivedBaseChangeMap_unit (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedMateUnitEquation (moduleInverseImageAdjunction f Λ)
      (moduleInverseImageAdjunction f' Λ)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom) K :=
  derivedMateUnitEquation_of_exactSquare (moduleInverseImageAdjunction f Λ)
    (moduleInverseImageAdjunction f' Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f f' g g' h).hom)
    (moduleDerivedInverseImageSquareIso_exactComparison Λ f f' g g' h) K

end AlgebraicGeometry.Scheme.EtaleCohomology
