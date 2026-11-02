/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.NatTrans
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualZeroComparison

/-! # Original derived exchange and its native unit

The original mate and its actual complex-unit equation are independent of the
ordinary higher-exchange interface. They retain one selected derived category
for each distinct sheaf category.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The canonical derived exchange map for a commuting square of schemes. -/
def derivedBaseChangeMap :
    derivedDirectImage f ⋙ derivedInverseImage g ⟶
      derivedInverseImage g' ⋙ derivedDirectImage f' :=
  (mateEquiv (derivedImageAdjunction f) (derivedImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans

/-- The exchange component retains the original derived unit and counit. -/
theorem derivedBaseChangeMap_app
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    MateComponentEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedInverseImageSquareIso f f' g g' h).hom K :=
  mateComponentEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedInverseImageSquareIso f f' g g' h).hom K

/-- The adjoint equation of the canonical derived exchange. -/
theorem derivedBaseChangeMap_counit
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    MateCounitEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedInverseImageSquareIso f f' g g' h).hom K :=
  mateCounitEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedInverseImageSquareIso f f' g g' h).hom K

/-- The adjoint equation characterizes the derived exchange, independently of resolutions. -/
theorem eq_derivedBaseChangeMap_iff
    (β : derivedDirectImage f ⋙ derivedInverseImage g ⟶
      derivedInverseImage g' ⋙ derivedDirectImage f') :
    β = derivedBaseChangeMap f f' g g' h ↔
      ∀ K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X),
        (derivedInverseImage f').map (β.app K) ≫
            (derivedImageAdjunction f').counit.app ((derivedInverseImage g').obj K) =
          (derivedInverseImageSquareIso f f' g g' h).hom.app
              ((derivedDirectImage f).obj K) ≫
            (derivedInverseImage g').map ((derivedImageAdjunction f).counit.app K) :=
  eq_mateEquiv_iff (derivedImageAdjunction f) (derivedImageAdjunction f') _ β

/-- Morphisms of derived coefficients commute with the canonical exchange. -/
@[reassoc]
theorem derivedBaseChangeMap_naturality
    {K L : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)} (a : K ⟶ L) :
    (derivedInverseImage g).map ((derivedDirectImage f).map a) ≫
        (derivedBaseChangeMap f f' g g' h).app L =
      (derivedBaseChangeMap f f' g g' h).app K ≫
        (derivedDirectImage f').map ((derivedInverseImage g').map a) :=
  (derivedBaseChangeMap f f' g g' h).naturality a


/-- The canonical derived exchange preserves the original right-derived units.
The shared formula retains the original degreewise underived exchange and both
exact inverse-image comparisons; no nonexact right-derived unit is cancelled. -/
theorem derivedBaseChangeMap_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    DerivedMateUnitEquation (inverseImageAdjunction f) (inverseImageAdjunction f')
      (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom) K :=
  derivedMateUnitEquation_of_exactSquare (inverseImageAdjunction f) (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (derivedInverseImageSquareIso_exactComparison f f' g g' h) K


omit [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original exchange is the literal ordinary adjunction mate. -/
theorem baseChangeMap_eq_mate :
    baseChangeMap f f' g g' h =
      (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
        (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)).natTrans := rfl

/-- The derived sheaf adjunction is the native right-derived adjunction. -/
theorem derivedImageAdjunction_eq_rightDerivedFunctorPlus :
    derivedImageAdjunction f = (inverseImageAdjunction f).rightDerivedFunctorPlus := rfl

/-- The derived exchange retains the native derived adjunctions explicitly. -/
theorem derivedBaseChangeMap_eq_nativeMate :
    derivedBaseChangeMap f f' g g' h =
      (mateEquiv (inverseImageAdjunction f).rightDerivedFunctorPlus
        (inverseImageAdjunction f').rightDerivedFunctorPlus
        (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans := by
  calc
    derivedBaseChangeMap f f' g g' h =
        (mateEquiv (derivedImageAdjunction f) (derivedImageAdjunction f')
          (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans := rfl
    _ = _ := congrArg₂ (fun a b =>
      (mateEquiv a b
        (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans)
      (derivedImageAdjunction_eq_rightDerivedFunctorPlus f)
      (derivedImageAdjunction_eq_rightDerivedFunctorPlus f')

/-- The higher-direct-image comparison is the original native comparison. -/
theorem higherDirectImageIso_eq_native (q : ℕ) :
    higherDirectImageIso f q = (directImage f).rightDerivedSingleHomologyIso q := rfl


/-- The original unit equation written using the actual canonical exchange maps. -/
theorem derivedBaseChangeMap_actualUnit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    Functor.ActualDerivedUnitEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) K :=
  actualDerivedUnitEquation_of_mate
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h)
    (baseChangeMap_eq_mate f f' g g' h) (derivedBaseChangeMap_eq_nativeMate f f' g g' h) K
    (derivedBaseChangeMap_unit f f' g g' h K)

end AlgebraicGeometry.Scheme.EtaleCohomology
