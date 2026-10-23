/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Postcomposition

/-!
# Exact direct image and its original derived functor

These are structural consumers of exactness of the original direct image, not
assertions that a geometric direct image is exact. The finite-morphism producer
can supply the explicit epimorphism-preservation hypothesis. All comparisons
retain the installed original right-derived unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For the original left exact direct image, preservation of epis suffices for exactness. -/
theorem directImage_preservesHomology_of_preservesEpimorphisms
    [(directImage f).PreservesEpimorphisms] : (directImage f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (directImage f)

/-- The same hypothesis supplies the native finite-colimit exactness interface. -/
theorem directImage_preservesFiniteColimits_of_preservesEpimorphisms
    [(directImage f).PreservesEpimorphisms] : PreservesFiniteColimits (directImage f) := by
  let : (directImage f).PreservesHomology :=
    directImage_preservesHomology_of_preservesEpimorphisms f
  exact Functor.preservesFiniteColimits_of_preservesHomology (directImage f)

variable [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [(directImage f).PreservesHomology]

/-- Exact direct image is computed termwise, through the original derived unit. -/
def derivedDirectImageExactComparison :
    DerivedCategory.Plus.Q ⋙ derivedDirectImage f ≅
      (directImage f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  (directImage f).rightDerivedFunctorPlusExactComparison

/-- Exact direct image carries the original single to the single of its image. -/
def derivedDirectImageSingleIso (i : ℤ) :
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) i ⋙
        derivedDirectImage f ≅
      directImage f ⋙ DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) i :=
  (directImage f).rightDerivedFunctorPlusSingleIso i

/-- Exact direct image commutes with every original bounded-below homology functor. -/
def derivedDirectImageHomologyIso (i : ℤ) :
    derivedDirectImage f ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) i ≅
      DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i ⋙ directImage f :=
  (directImage f).rightDerivedFunctorPlusHomologyIso i

/-- Positive original higher direct images vanish when the actual direct image is exact. -/
theorem isZero_higherDirectImage_obj_of_preservesHomology
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj F) := by
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)
  let e := (higherDirectImageIso f q).app F ≪≫
    H.mapIso ((derivedDirectImageSingleIso f 0).app F)
  apply IsZero.of_iso _ e
  exact DerivedCategory.Plus.isZero_homology_of_isLE
    ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
      ((directImage f).obj F)) 0 (q : ℤ) (by exact_mod_cast hq)

end AlgebraicGeometry.Scheme.EtaleCohomology
