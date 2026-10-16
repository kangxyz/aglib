/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Native derived direct image and open restriction

The original ordinary cartesian open comparison induces an isomorphism
between the installed derived functors. Exactness of target restriction
and preservation of injectives by source restriction supply the two
native derived-composition comparisons. Their original units determine
the resulting map. Taking homology computes restriction of the actual
natural-degree higher direct images, without a geometric finiteness or
quasicoherence assumption.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- All comparisons use the installed standard derived categories of actual module sheaves. -/
local instance openHigherImageStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

/-- Original cartesian open restriction commutes with the installed bounded-below derived
pushforward, through the original two native composition comparisons. -/
def derivedOpenBaseChangeIso :
    (pushforward f).rightDerivedFunctorPlus ⋙ (restrictFunctor j).rightDerivedFunctorPlus ≅
      (restrictFunctor a).rightDerivedFunctorPlus ⋙ (pushforward b).rightDerivedFunctorPlus :=
  ((pushforward f).rightDerivedFunctorPlusCompIsoOfPreservesHomology (restrictFunctor j)).symm ≪≫
    (pushforward f ⋙ restrictFunctor j).rightDerivedFunctorPlusIso
      (cartesianOpenBaseChange a b f j h) ≪≫
    (restrictFunctor a).rightDerivedFunctorPlusCompIsoOfPreservesInjectives (pushforward b)

/-- The actual derived open comparison preserves the original ordinary cartesian comparison
and the actual installed composite-derived units. -/
@[reassoc]
theorem derivedOpenBaseChangeIso_unit (K : CochainComplex.Plus U.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor j)).app K ≫
        (derivedOpenBaseChangeIso a b f j h).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h)).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor a) (pushforward b)).app K := by
  let F : U.Modules ⥤ X.Modules := pushforward f
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let A : U.Modules ⥤ W.Modules := restrictFunctor a
  let B : W.Modules ⥤ V.Modules := pushforward b
  let eL := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology J
  let eM := (F ⋙ J).rightDerivedFunctorPlusIso (cartesianOpenBaseChange a b f j h)
  let eR := A.rightDerivedFunctorPlusCompIsoOfPreservesInjectives B
  have hL : (F ⋙ J).rightDerivedFunctorPlusUnit.app K ≫
      eL.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit F J).app K := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    exact F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app J K
  have hM := (F ⋙ J).rightDerivedFunctorPlusIso_hom_app
    (cartesianOpenBaseChange a b f j h) K
  have hR : (A ⋙ B).rightDerivedFunctorPlusUnit.app K ≫
      eR.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit A B).app K := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    exact A.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app B K
  change (Functor.rightDerivedFunctorPlusCompUnit F J).app K ≫
      eL.inv.app (DerivedCategory.Plus.Q.obj K) ≫
      eM.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      eR.hom.app (DerivedCategory.Plus.Q.obj K) = _
  rw [← hL]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hM]
  simp only [Category.assoc]
  rw [hR]

/-- The actual natural-degree higher direct image commutes with cartesian open restriction.
Every comparison is homology of the original derived open comparison and exact restriction. -/
def higherDirectImageOpenRestrictionIso (n : ℕ) :
    (pushforward f).rightDerived n ⋙ restrictFunctor j ≅
      restrictFunctor a ⋙ (pushforward b).rightDerived n := by
  let F : U.Modules ⥤ X.Modules := pushforward f
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let A : U.Modules ⥤ W.Modules := restrictFunctor a
  let B : W.Modules ⥤ V.Modules := pushforward b
  let S := DerivedCategory.Plus.singleFunctor U.Modules 0
  let T := DerivedCategory.Plus.singleFunctor W.Modules 0
  let H := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let eF := F.rightDerivedSingleHomologyIso n
  let eJ := J.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let eA := A.rightDerivedFunctorPlusSingleIso 0
  let eB := B.rightDerivedSingleHomologyIso n
  exact Functor.isoWhiskerRight eF J ≪≫
    Functor.associator S _ J ≪≫
    Functor.isoWhiskerLeft S (Functor.associator F.rightDerivedFunctorPlus _ J) ≪≫
    Functor.isoWhiskerLeft S
      (Functor.isoWhiskerLeft F.rightDerivedFunctorPlus eJ.symm) ≪≫
    Functor.isoWhiskerLeft S
      (Functor.associator F.rightDerivedFunctorPlus J.rightDerivedFunctorPlus H).symm ≪≫
    (Functor.associator S (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus) H).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft S (derivedOpenBaseChangeIso a b f j h)) H ≪≫
    Functor.isoWhiskerRight
      (Functor.associator S A.rightDerivedFunctorPlus B.rightDerivedFunctorPlus).symm H ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight eA B.rightDerivedFunctorPlus) H ≪≫
    Functor.associator (A ⋙ T) B.rightDerivedFunctorPlus H ≪≫
    Functor.associator A T (B.rightDerivedFunctorPlus ⋙ H) ≪≫
    Functor.isoWhiskerLeft A eB.symm

/-- Restriction to an actual target open commutes with the original derived direct image. -/
abbrev derivedPushforwardRestrictionIso {Y Z : Scheme.{u}} (p : Y ⟶ Z) (O : Z.Opens) :
    (pushforward p).rightDerivedFunctorPlus ⋙ (restrictFunctor O.ι).rightDerivedFunctorPlus ≅
      (restrictFunctor (p ⁻¹ᵁ O).ι).rightDerivedFunctorPlus ⋙
        (pushforward (p ∣_ O)).rightDerivedFunctorPlus :=
  derivedOpenBaseChangeIso (p ⁻¹ᵁ O).ι (p ∣_ O) p O.ι
    (isPullback_morphismRestrict p O).flip

/-- Restriction to an actual target open commutes with the actual original higher direct image. -/
abbrev higherDirectImageRestrictionIso {Y Z : Scheme.{u}} (p : Y ⟶ Z) (O : Z.Opens) (n : ℕ) :
    (pushforward p).rightDerived n ⋙ restrictFunctor O.ι ≅
      restrictFunctor (p ⁻¹ᵁ O).ι ⋙ (pushforward (p ∣_ O)).rightDerived n :=
  higherDirectImageOpenRestrictionIso (p ⁻¹ᵁ O).ι (p ∣_ O) p O.ι
    (isPullback_morphismRestrict p O).flip n

end AlgebraicGeometry.Scheme.Modules
