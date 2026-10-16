/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Injective.MapAugmentation
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution

/-!
# The original derived unit on an acyclic coefficient

For a left exact additive functor, vanishing of its original positive
right-derived objects on one coefficient makes the installed derived
unit invertible on that coefficient's native single. The resulting
comparison uses the inverse of this same unit and the original
single-complex comparison. Exactness on all objects is not assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v u' v' w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w'} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

namespace InjectiveResolution

/-- Every supplied original resolution proves invertibility of the same installed
derived unit on an acyclic coefficient. -/
theorem isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ
    {M : C} (I : InjectiveResolution M)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus C 0).obj M)) := by
  have hI := I.map_ι'_quasiIso_of_isZero_rightDerived_succ F hM
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map I.ιPlus)) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso D)
      (F.mapCochainComplexPlus.map I.ιPlus) hI
  rw [← I.rightDerivedFunctorPlusIso_unit F]
  infer_instance

end InjectiveResolution

namespace Functor

/-- The original derived unit is invertible on a single coefficient with vanishing
positive right-derived objects. -/
theorem isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ
    (M : C) (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus C 0).obj M)) :=
  (injectiveResolution M).isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ F hM

/-- The installed right-derived functor of a left exact additive functor on an acyclic
coefficient is the original single of its image. -/
def rightDerivedFunctorPlusSingleIsoOfAcyclic (M : C)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (F.obj M) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ M hM
  let E : F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) ≅
      (CochainComplex.singleFunctorPlus D 0).obj (F.obj M) :=
    (CochainComplex.plus D).isoMk ((singleMapHomologicalComplex F (.up ℤ) 0).app M)
  exact (asIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus C 0).obj M))).symm ≪≫
    DerivedCategory.Plus.Q.mapIso E

/-- The comparison retains the original installed derived unit and actual
single-complex comparison. -/
@[reassoc]
theorem rightDerivedFunctorPlusSingleIsoOfAcyclic_unit (M : C)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M)) :
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M) ≫
        (rightDerivedFunctorPlusSingleIsoOfAcyclic F M hM).hom =
      DerivedCategory.Plus.Q.map
        (show F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) ⟶
            (CochainComplex.singleFunctorPlus D 0).obj (F.obj M) from
          ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ M hM
  change F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M) ≫
    CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus C 0).obj M)) ≫ _ = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rfl

/-- The original derived coefficient map agrees with the native single coefficient
map under these coefficient-specific comparisons. -/
@[reassoc]
theorem rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality
    {M N : C} (f : M ⟶ N)
    (hM : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj M))
    (hN : ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj N)) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (rightDerivedFunctorPlusSingleIsoOfAcyclic F N hN).hom =
      (rightDerivedFunctorPlusSingleIsoOfAcyclic F M hM).hom ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (F.map f) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ M hM
  have hU := F.rightDerivedFunctorPlusUnit.naturality
    ((CochainComplex.singleFunctorPlus C 0).map f)
  change DerivedCategory.Plus.Q.map
      (F.mapCochainComplexPlus.map ((CochainComplex.singleFunctorPlus C 0).map f)) ≫
        F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj N) =
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M) ≫
        F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) at hU
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app
    ((CochainComplex.singleFunctorPlus C 0).obj M))).mp
  erw [← Category.assoc, ← hU, Category.assoc,
    rightDerivedFunctorPlusSingleIsoOfAcyclic_unit,
    rightDerivedFunctorPlusSingleIsoOfAcyclic_unit_assoc]
  have h : F.mapCochainComplexPlus.map ((CochainComplex.singleFunctorPlus C 0).map f) ≫
      (show F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj N) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj (F.obj N) from
        ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app N)) =
      (show F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) ⟶
          (CochainComplex.singleFunctorPlus D 0).obj (F.obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
        (CochainComplex.singleFunctorPlus D 0).map (F.map f) := by
    apply ObjectProperty.hom_ext
    exact (singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality f
  change DerivedCategory.Plus.Q.map
      (F.mapCochainComplexPlus.map ((CochainComplex.singleFunctorPlus C 0).map f)) ≫
        DerivedCategory.Plus.Q.map _ =
      DerivedCategory.Plus.Q.map _ ≫
        DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus D 0).map (F.map f))
  simpa only [Functor.map_comp] using congrArg DerivedCategory.Plus.Q.map h

end Functor

end CategoryTheory
