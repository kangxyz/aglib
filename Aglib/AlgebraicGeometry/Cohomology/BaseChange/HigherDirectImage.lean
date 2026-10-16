/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Flat base change for the actual higher direct images

The native higher-image comparison is homology of the original derived
base-change map on the native coefficient single, through the installed
single and exact-pullback homology comparisons. It is a natural
transformation on actual module sheaves. For a qcqs direct-image morphism
and quasicoherent coefficients, every component is invertible after flat
base change, on arbitrary base schemes.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Retain the installed standard derived categories of actual module sheaves. -/
local instance higherImageBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original derived flat comparison is invertible on a quasicoherent coefficient single
in every integer degree over an arbitrary target. -/
theorem derivedFlatBaseChangeMap_isIso_single
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] [QuasiCompact f] [QuasiSeparated f]
    (M : U.Modules) [M.IsQuasicoherent] (i : ℤ) :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules i).obj M)) := by
  apply derivedFlatBaseChangeMap_isIso_of_quasicoherent_homology a b f j h
  intro n
  by_cases hn : n = i
  · subst n
    exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := U.Modules) i).app M).symm
      (inferInstanceAs M.IsQuasicoherent)
  · have hz : IsZero ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
        ((DerivedCategory.Plus.singleFunctor U.Modules i).obj M)) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ i n hn
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ i n hn
    exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_isLimit hz.isTerminal
      (by rintro ⟨⟨⟩⟩)

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]

/-- The actual higher-direct-image comparison is homology of the original derived mate,
through the original installed single and exact-pullback comparisons. -/
def higherDirectImageFlatBaseChangeMap (n : ℕ) :
    (pushforward f).rightDerived n ⋙ pullback j ⟶
      pullback a ⋙ (pushforward b).rightDerived n := by
  letI := flat_cartesian_baseChange a b f j h
  let F : U.Modules ⥤ X.Modules := pushforward f
  let J : X.Modules ⥤ V.Modules := pullback j
  let A : U.Modules ⥤ W.Modules := pullback a
  let B : W.Modules ⥤ V.Modules := pushforward b
  let S := DerivedCategory.Plus.singleFunctor U.Modules 0
  let T := DerivedCategory.Plus.singleFunctor W.Modules 0
  let H := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let eF := F.rightDerivedSingleHomologyIso n
  let eJ := J.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let eA := A.rightDerivedFunctorPlusSingleIso 0
  let eB := B.rightDerivedSingleHomologyIso n
  let eL : F.rightDerived n ⋙ J ≅
      (S ⋙ (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus)) ⋙ H :=
    Functor.isoWhiskerRight eF J ≪≫
      Functor.associator S _ J ≪≫
      Functor.isoWhiskerLeft S (Functor.associator F.rightDerivedFunctorPlus _ J) ≪≫
      Functor.isoWhiskerLeft S
        (Functor.isoWhiskerLeft F.rightDerivedFunctorPlus eJ.symm) ≪≫
      Functor.isoWhiskerLeft S
        (Functor.associator F.rightDerivedFunctorPlus J.rightDerivedFunctorPlus H).symm ≪≫
      (Functor.associator S (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus) H).symm
  let eR : (S ⋙ (A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus)) ⋙ H ≅
      A ⋙ B.rightDerived n :=
    Functor.isoWhiskerRight
      (Functor.associator S A.rightDerivedFunctorPlus B.rightDerivedFunctorPlus).symm H ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight eA B.rightDerivedFunctorPlus) H ≪≫
      Functor.associator (A ⋙ T) B.rightDerivedFunctorPlus H ≪≫
      Functor.associator A T (B.rightDerivedFunctorPlus ⋙ H) ≪≫
      Functor.isoWhiskerLeft A eB.symm
  exact eL.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft S (derivedFlatBaseChangeMap a b f j h)) H ≫
      eR.hom

/-- Every higher-image component is the literal homology map of the same original derived
comparison, conjugated by the original native single and exact-pullback homology isomorphisms. -/
theorem higherDirectImageFlatBaseChangeMap_app (n : ℕ) (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    (higherDirectImageFlatBaseChangeMap a b f j h n).app M =
      (pullback j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((pullback j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((derivedPushforwardPlus f).obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((derivedFlatBaseChangeMap a b f j h).app
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((derivedPushforwardPlus b).map
            (((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((pullback a).obj M) := by
  let := flat_cartesian_baseChange a b f j h
  simp only [higherDirectImageFlatBaseChangeMap, derivedPushforwardPlus,
    CategoryTheory.Functor.map_id, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp, Category.assoc]
  erw [Category.id_comp]

/-- Flat base change for the actual native higher direct images of quasicoherent modules
under a qcqs morphism, over arbitrary target schemes and in every natural degree. -/
theorem higherDirectImageFlatBaseChangeMap_isIso_app [QuasiCompact f] [QuasiSeparated f]
    (M : U.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((higherDirectImageFlatBaseChangeMap a b f j h n).app M) := by
  let := flat_cartesian_baseChange a b f j h
  let : IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) :=
    derivedFlatBaseChangeMap_isIso_single a b f j h M 0
  rw [higherDirectImageFlatBaseChangeMap_app]
  infer_instance

/-- The higher-image flat base-change isomorphism has the original higher-image map as its
forward arrow. Its inverse is the inverse of that same proved component. -/
def higherDirectImageFlatBaseChangeIso [QuasiCompact f] [QuasiSeparated f]
    (M : U.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (pullback j).obj (((pushforward f).rightDerived n).obj M) ≅
      ((pushforward b).rightDerived n).obj ((pullback a).obj M) := by
  letI := higherDirectImageFlatBaseChangeMap_isIso_app a b f j h M n
  exact asIso ((higherDirectImageFlatBaseChangeMap a b f j h n).app M)

/-- The higher-image isomorphism retains exactly the original canonical comparison. -/
@[simp]
theorem higherDirectImageFlatBaseChangeIso_hom [QuasiCompact f] [QuasiSeparated f]
    (M : U.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (higherDirectImageFlatBaseChangeIso a b f j h M n).hom =
      (higherDirectImageFlatBaseChangeMap a b f j h n).app M := rfl

end AlgebraicGeometry.Scheme.Modules
