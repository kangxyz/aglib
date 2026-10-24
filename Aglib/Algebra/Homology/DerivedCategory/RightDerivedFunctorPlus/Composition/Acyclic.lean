/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.DerivedCategory.Plus.InjectiveComparison
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Comparison
public import Aglib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# Original derived composition under acyclicity of injective images

For additive functors `F : A ⥤ B` and `G : B ⥤ C`, the original composite
unit determines the canonical comparison from `R(F ⋙ G)` to `RF ⋙ RG`.
When `G` is left exact and `F` sends injectives to objects with vanishing
positive right-derived objects under `G`, this same comparison is invertible.

The proof first checks injective singles using the original units, then all
singles by injective presentations, and finally arbitrary bounded-below
objects by finite Postnikov truncations in each degree. No preservation of
injectives by `F`, upper bound, or cohomological-dimension bound is assumed.
The category, morphism and derived-category universes are independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [EnoughInjectives B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]

/-- The canonical comparison determined by the original derived composition unit.
Its construction requires neither left exactness nor acyclicity. -/
def rightDerivedFunctorPlusCompComparison :
    (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  rightDerivedNatTrans (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
    (CochainComplex.Plus.quasiIso A) (𝟙 _)

/-- The canonical comparison retains the two original units in their original order. -/
@[reassoc]
theorem rightDerivedFunctorPlusCompComparison_app (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompComparison F G).app (DerivedCategory.Plus.Q.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  simpa only [rightDerivedFunctorPlusCompComparison, NatTrans.id_app, Category.id_comp,
    rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (CochainComplex.Plus.quasiIso A) (𝟙 _) K

/-- The original canonical composition comparison commutes with native shifts. -/
instance rightDerivedFunctorPlusCompComparison_commShift :
    (rightDerivedFunctorPlusCompComparison F G).CommShift ℤ := by
  dsimp only [rightDerivedFunctorPlusCompComparison, rightDerivedNatTrans]
  infer_instance

variable [PreservesFiniteLimits G]

/-- Acyclicity of the image of one injective makes the original comparison
invertible on that injective's original degree-zero single. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_app_single_of_injective
    (I : A) [Injective I]
    (hI : ∀ n : ℕ, IsZero ((G.rightDerived (n + 1)).obj (F.obj I))) :
    IsIso ((rightDerivedFunctorPlusCompComparison F G).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj I)) := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj I
  have hK (n : ℤ) : Injective (K.obj.X n) := by
    change Injective (((HomologicalComplex.single A (.up ℤ) 0).obj I).X n)
    infer_instance
  let := F.isIso_rightDerivedFunctorPlusUnit_of_injective K hK
  let := (F ⋙ G).isIso_rightDerivedFunctorPlusUnit_of_injective K hK
  let e : F.mapCochainComplexPlus.obj K ≅
      (CochainComplex.singleFunctorPlus B 0).obj (F.obj I) :=
    (CochainComplex.plus B).isoMk ((singleMapHomologicalComplex F (.up ℤ) 0).app I)
  have : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K)) :=
    (NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnit e).mpr
      (G.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ (F.obj I) hI)
  change IsIso ((rightDerivedFunctorPlusCompComparison F G).app
    (DerivedCategory.Plus.Q.obj K))
  apply (isIso_comp_left_iff ((F ⋙ G).rightDerivedFunctorPlusUnit.app K) _).mp
  rw [rightDerivedFunctorPlusCompComparison_app]
  infer_instance

/-- Acyclicity of all injective images makes the original canonical comparison
invertible on every coefficient single. No injective-preservation premise is used. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_app_single_of_acyclic
    (hI : ∀ (I : A) [Injective I] (n : ℕ),
      IsZero ((G.rightDerived (n + 1)).obj (F.obj I))) (M : A) :
    IsIso ((rightDerivedFunctorPlusCompComparison F G).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)) := by
  apply DerivedCategory.Plus.InjectiveComparison.isIso_app_single_of_injective
    (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (rightDerivedFunctorPlusCompComparison F G)
  · intro Y
    exact (F ⋙ G).rightDerivedFunctorPlus_isGE _ 0
  · intro Y
    let := F.rightDerivedFunctorPlus_isGE
      ((DerivedCategory.Plus.singleFunctor A 0).obj Y) 0
    exact G.rightDerivedFunctorPlus_isGE _ 0
  · intro I h
    exact isIso_rightDerivedFunctorPlusCompComparison_app_single_of_injective F G I (hI I)

/-- The original canonical composition comparison is invertible on all of `D+`
when the first functor sends injectives to acyclic objects for the second functor. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_of_acyclic
    (hI : ∀ (I : A) [Injective I] (n : ℕ),
      IsZero ((G.rightDerived (n + 1)).obj (F.obj I))) :
    IsIso (rightDerivedFunctorPlusCompComparison F G) := by
  apply DerivedCategory.Plus.isIso_of_singles (rightDerivedFunctorPlusCompComparison F G)
  · intro X a hX
    let : X.IsGE a := hX
    exact (F ⋙ G).rightDerivedFunctorPlus_isGE X a
  · intro X a hX
    let : X.IsGE a := hX
    let := F.rightDerivedFunctorPlus_isGE X a
    exact G.rightDerivedFunctorPlus_isGE _ a
  · intro M i
    let e := ((DerivedCategory.Plus.singleFunctors A).shiftIso (-i) i 0 (by omega)).app M
    rw [← NatTrans.isIso_app_iff_of_iso (rightDerivedFunctorPlusCompComparison F G) e]
    dsimp only [Functor.comp_obj]
    rw [NatTrans.app_shift]
    have : IsIso ((rightDerivedFunctorPlusCompComparison F G).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M)) :=
      isIso_rightDerivedFunctorPlusCompComparison_app_single_of_acyclic F G hI M
    infer_instance

/-- The canonical natural isomorphism of the installed right-derived functors
under actual acyclicity of the images of injective objects. -/
def rightDerivedFunctorPlusCompIsoOfAcyclic
    (hI : ∀ (I : A) [Injective I] (n : ℕ),
      IsZero ((G.rightDerived (n + 1)).obj (F.obj I))) :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus := by
  let := isIso_rightDerivedFunctorPlusCompComparison_of_acyclic F G hI
  exact asIso (rightDerivedFunctorPlusCompComparison F G)

/-- The acyclic-image composition isomorphism retains the original unit equation. -/
@[reassoc]
theorem rightDerivedFunctorPlusCompIsoOfAcyclic_hom_app
    (hI : ∀ (I : A) [Injective I] (n : ℕ),
      IsZero ((G.rightDerived (n + 1)).obj (F.obj I))) (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIsoOfAcyclic F G hI).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) :=
  rightDerivedFunctorPlusCompComparison_app F G K

end CategoryTheory.Functor
