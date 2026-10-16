/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Modification.Unit
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
# The original modification map under open restriction

The original ordinary open mate and installed derived open comparison
retain the same single-complex maps and derived units. These identities
identify restriction of the canonical ordinary modification map with the
corresponding canonical map in the supplied open cartesian square.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance modificationRestrictionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {W Y V X : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ V) (π : Y ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b π j)

/-- The original open comparison commutes with the original native single-complex
maps. The equality is literal in bounded-below module complexes. -/
theorem cartesianOpenBaseChange_singleComplex (N : Y.Modules) :
    (restrictFunctor j).mapCochainComplexPlus.map
        ((exactSingleComplexNatIso (pushforward π)).inv.app N) ≫
      (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b π j h)).hom.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N) ≫
      (pushforward b).mapCochainComplexPlus.map
        ((exactSingleComplexNatIso (restrictFunctor a)).hom.app N) =
    (exactSingleComplexNatIso (restrictFunctor j)).hom.app ((pushforward π).obj N) ≫
      (CochainComplex.singleFunctorPlus V.Modules 0).map
        ((cartesianOpenBaseChange a b π j h).hom.app N) ≫
      (exactSingleComplexNatIso (pushforward b)).inv.app ((restrictFunctor a).obj N) := by
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [Functor.comp_obj, Functor.mapCochainComplexPlus_obj_obj_X,
      ObjectProperty.FullSubcategory.comp_hom, comp_f, Functor.mapCochainComplexPlus_map_hom_f]
    change (restrictFunctor j).map ((pushforward π).map (𝟙 N)) ≫
        (cartesianOpenBaseChange a b π j h).hom.app N ≫
          (pushforward b).map (𝟙 ((restrictFunctor a).obj N)) =
      𝟙 _ ≫ (cartesianOpenBaseChange a b π j h).hom.app N ≫
        𝟙 _ ≫ (pushforward b).map (𝟙 ((restrictFunctor a).obj N))
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  · have hzero : IsZero
        (((restrictFunctor j).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj
            ((pushforward π).obj N))).obj.X n) :=
      (restrictFunctor j).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 ((pushforward π).obj N) n hn)
    exact hzero.eq_of_src _ _

private theorem cartesianOpenBaseChange_singleUnit (N : Y.Modules) :
    (restrictFunctor j).rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus X.Modules 0).obj ((pushforward π).obj N)) ≫
      (restrictFunctor j).rightDerivedFunctorPlus.map
        ((rightDerivedSingleComparison (pushforward π)).app N) ≫
      (derivedOpenBaseChangeIso a b π j h).hom.app
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) =
    DerivedCategory.Plus.Q.map
        ((restrictFunctor j).mapCochainComplexPlus.map
            ((exactSingleComplexNatIso (pushforward π)).inv.app N) ≫
          (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b π j h)).hom.app
            ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) ≫
      (pushforward b).rightDerivedFunctorPlusUnit.app
        ((restrictFunctor a).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        ((restrictFunctor a).rightDerivedFunctorPlusUnit.app
          ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) := by
  let F : Y.Modules ⥤ X.Modules := pushforward π
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let A : Y.Modules ⥤ W.Modules := restrictFunctor a
  let B : W.Modules ⥤ V.Modules := pushforward b
  let K := (CochainComplex.singleFunctorPlus Y.Modules 0).obj N
  let S := (exactSingleComplexNatIso F).inv.app N
  have hBC := derivedOpenBaseChangeIso_unit a b π j h K
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at hBC
  have hJ := J.rightDerivedFunctorPlusUnit.naturality S
  simp only [Functor.comp_map] at hJ
  change J.rightDerivedFunctorPlusUnit.app _ ≫
      J.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map S ≫ F.rightDerivedFunctorPlusUnit.app K) ≫ _ = _
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hJ, hBC]

private theorem cartesianOpenBaseChange_singleUnitTarget (N : Y.Modules) :
    DerivedCategory.Plus.Q.map
        ((restrictFunctor j).mapCochainComplexPlus.map
            ((exactSingleComplexNatIso (pushforward π)).inv.app N) ≫
          (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b π j h)).hom.app
            ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) ≫
      (pushforward b).rightDerivedFunctorPlusUnit.app
        ((restrictFunctor a).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        ((restrictFunctor a).rightDerivedFunctorPlusUnit.app
          ((CochainComplex.singleFunctorPlus Y.Modules 0).obj N)) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app N) =
    DerivedCategory.Plus.Q.map
        ((exactSingleComplexNatIso (restrictFunctor j)).hom.app ((pushforward π).obj N)) ≫
      (DerivedCategory.Plus.singleFunctor V.Modules 0).map
        ((cartesianOpenBaseChange a b π j h).hom.app N) ≫
      (rightDerivedSingleComparison (pushforward b)).app ((restrictFunctor a).obj N) := by
  let A : Y.Modules ⥤ W.Modules := restrictFunctor a
  let B : W.Modules ⥤ V.Modules := pushforward b
  let K := (CochainComplex.singleFunctorPlus Y.Modules 0).obj N
  let SA := (exactSingleComplexNatIso A).app N
  have hB := B.rightDerivedFunctorPlusUnit.naturality SA.hom
  simp only [Functor.comp_map] at hB
  have hA := A.rightDerivedFunctorPlusSingleIso_unit 0 N
  change A.rightDerivedFunctorPlusUnit.app K ≫
      ((A.rightDerivedFunctorPlusSingleIso 0).hom.app N) =
    DerivedCategory.Plus.Q.map SA.hom at hA
  erw [← B.rightDerivedFunctorPlus.map_comp, hA, ← hB]
  have hs := cartesianOpenBaseChange_singleComplex a b π j h N
  have hQ := congrArg
    (fun q => DerivedCategory.Plus.Q.map q ≫ B.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus W.Modules 0).obj (A.obj N))) hs
  change _ =
    DerivedCategory.Plus.Q.map
        ((exactSingleComplexNatIso (restrictFunctor j)).hom.app ((pushforward π).obj N)) ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus V.Modules 0).map
        ((cartesianOpenBaseChange a b π j h).hom.app N)) ≫
      DerivedCategory.Plus.Q.map ((exactSingleComplexNatIso B).inv.app (A.obj N)) ≫
      B.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus W.Modules 0).obj (A.obj N))
  simp only [Functor.map_comp, Category.assoc] at hQ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  exact hQ

/-- The original right-derived single comparison commutes with the actual
cartesian open comparison and the original exact restriction-single maps. -/
theorem cartesianOpenBaseChange_derivedSingleComparison (N : Y.Modules) :
    (restrictFunctor j).rightDerivedFunctorPlus.map
        ((rightDerivedSingleComparison (pushforward π)).app N) ≫
      (derivedOpenBaseChangeIso a b π j h).hom.app
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app N) =
    (((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).hom.app
        ((pushforward π).obj N)) ≫
      (DerivedCategory.Plus.singleFunctor V.Modules 0).map
        ((cartesianOpenBaseChange a b π j h).hom.app N) ≫
      (rightDerivedSingleComparison (pushforward b)).app ((restrictFunctor a).obj N) := by
  let F : Y.Modules ⥤ X.Modules := pushforward π
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let := J.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (cancel_epi (J.rightDerivedFunctorPlusUnit.app
    ((CochainComplex.singleFunctorPlus X.Modules 0).obj (F.obj N)))).mp
  erw [reassoc_of% cartesianOpenBaseChange_singleUnit a b π j h N,
    cartesianOpenBaseChange_singleUnitTarget a b π j h N,
    reassoc_of% J.rightDerivedFunctorPlusSingleIso_unit 0 (F.obj N)]
  rfl

/-- Restriction of the original ordinary modification map is the local
ordinary modification map, through the original open derived comparison,
exact restriction-single comparisons and ordinary pullback mate. -/
theorem ordinaryModificationUnit_open_restriction (M : X.Modules) :
    (restrictFunctor j).rightDerivedFunctorPlus.map (ordinaryModificationUnit π M) ≫
      (derivedOpenBaseChangeIso a b π j h).hom.app
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((pullback π).obj M)) =
    (((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
      ordinaryModificationUnit b ((restrictFunctor j).obj M) ≫
      (pushforward b).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).map
          ((cartesianPullbackBaseChangeMate a b π j h).app M)) := by
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let B : W.Modules ⥤ V.Modules := pushforward b
  let η := (pullbackPushforwardAdjunction π).unit.app M
  let m := (cartesianPullbackBaseChangeMate a b π j h).app M
  have hD := cartesianOpenBaseChange_derivedSingleComparison a b π j h ((pullback π).obj M)
  have hJ := ((J.rightDerivedFunctorPlusSingleIso 0).hom.naturality η)
  have hB := (rightDerivedSingleComparison B).naturality m
  simp only [Functor.comp_map] at hJ hB
  have hunit := cartesianOpenBaseChange_pullback_unit a b π j h M
  have hmap := congrArg ((DerivedCategory.Plus.singleFunctor V.Modules 0).map) hunit
  simp only [Functor.map_comp] at hmap
  rw [ordinaryModificationUnit_eq, ordinaryModificationUnit_eq]
  simp only [Functor.map_comp, Category.assoc]
  erw [hD, reassoc_of% hJ]
  erw [reassoc_of% hmap, hB]
  rfl

include h in
/-- Over a supplied open square where the restricted morphism is an
isomorphism, the actual restriction of the original modification map is
invertible for every module coefficient. -/
theorem ordinaryModificationUnit_open_isIso [IsIso b] (M : X.Modules) :
    IsIso ((restrictFunctor j).rightDerivedFunctorPlus.map (ordinaryModificationUnit π M)) := by
  let := ordinaryModificationUnit_isIso_of_isIso b ((restrictFunctor j).obj M)
  have heq := ordinaryModificationUnit_open_restriction a b π j h M
  have hr : IsIso
      ((((restrictFunctor j).rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
        ordinaryModificationUnit b ((restrictFunctor j).obj M) ≫
        (pushforward b).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor W.Modules 0).map
            ((cartesianPullbackBaseChangeMate a b π j h).app M))) := by infer_instance
  have hc : IsIso
      ((restrictFunctor j).rightDerivedFunctorPlus.map (ordinaryModificationUnit π M) ≫
        (derivedOpenBaseChangeIso a b π j h).hom.app
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pullback π).obj M)) ≫
        (pushforward b).rightDerivedFunctorPlus.map
          (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app
            ((pullback π).obj M))) := heq.symm ▸ hr
  exact IsIso.of_isIso_comp_right
    ((restrictFunctor j).rightDerivedFunctorPlus.map (ordinaryModificationUnit π M))
    ((derivedOpenBaseChangeIso a b π j h).hom.app _ ≫
      (pushforward b).rightDerivedFunctorPlus.map
        (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app _))

/-- The native inverse-image open gives the isomorphism-locus specialization
of the same original modification map. -/
theorem ordinaryModificationUnit_restrict_isIso (U : X.Opens) [IsIso (π ∣_ U)]
    (M : X.Modules) :
    IsIso ((restrictFunctor U.ι).rightDerivedFunctorPlus.map (ordinaryModificationUnit π M)) :=
  ordinaryModificationUnit_open_isIso (π ⁻¹ᵁ U).ι (π ∣_ U) π U.ι
    (isPullback_morphismRestrict π U).flip M

end AlgebraicGeometry.Scheme.Modules
