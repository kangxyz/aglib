/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Basic
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# The unbounded derived adjunction for an exact left adjoint

The K-injective derivability criterion proves that the right-derived functor
is absolute. The native derived-adjunction construction therefore gives the
adjunction with the existing localization of an exact left adjoint. Its unit
and counit equations retain the original degreewise adjunction maps.

Only the right-adjoint source needs the explicitly supplied replacement.
-/

@[expose] public noncomputable section

universe u v w u' v' w' u'' v''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
  (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)
  {E : Type u''} [Category.{v''} E] (H : DerivedCategory D ⥤ E)

/-- The right-derived functor from K-injectives remains right-derived after
 arbitrary postcomposition. This is the absoluteness required for adjunctions. -/
lemma rightDerivedFunctorOfKInjectiveReplacement_postcomp_isRightDerivedFunctor :
    (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR ⋙ H).IsRightDerivedFunctor
      (whiskerRight (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR) H ≫
        (associator _ _ _).hom)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have := CochainComplex.isRightDerivabilityStructure_of_kInjectiveReplacement R η hη hR
  have h : (CochainComplex.kInjectiveLocalizerMorphism C).Derives
      ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ H) :=
    MorphismProperty.IsInvertedBy.of_comp _ _
      (CochainComplex.kInjectiveLocalizerMorphism_derives F) H
  apply h.isRightDerivedFunctor_of_isIso
  intro I
  have : I.obj.IsKInjective := I.property
  dsimp
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
  (η : 𝟭 (CochainComplex D ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)

/-- The native localization of an exact functor is also its left-derived functor. -/
lemma exact_isLeftDerivedFunctor :
    F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso C (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors

/-- Exact localization remains left-derived after postcomposition with the right-derived functor. -/
lemma exact_postcomp_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor
      (F.mapDerivedCategory ⋙ G.rightDerivedFunctorOfKInjectiveReplacement R η hη hR)
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight F.mapDerivedCategoryFactors.hom
            (G.rightDerivedFunctorOfKInjectiveReplacement R η hη hR))
        (HomologicalComplex.quasiIso C (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _)

/-- The actual unbounded right-derived adjunction with the native localization
 of the exact left adjoint. No replacement is needed on its source category. -/
def rightDerivedAdjunctionOfKInjectiveReplacement :
    F.mapDerivedCategory ⊣ G.rightDerivedFunctorOfKInjectiveReplacement R η hη hR := by
  have := exact_isLeftDerivedFunctor (F := F)
  have := exact_postcomp_isLeftDerivedFunctor (F := F) (G := G) R η hη hR
  have := G.rightDerivedFunctorOfKInjectiveReplacement_postcomp_isRightDerivedFunctor
    R η hη hR F.mapDerivedCategory
  exact (adj.mapHomologicalComplex (.up ℤ)).derived
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategoryFactors.hom
    (G.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR)

/-- The derived unit is induced by the original degreewise adjunction unit. -/
@[reassoc]
lemma rightDerivedAdjunctionOfKInjectiveReplacement_unit_app (K : CochainComplex C ℤ) :
    (adj.rightDerivedAdjunctionOfKInjectiveReplacement R η hη hR).unit.app
        (DerivedCategory.Q.obj K) ≫
      (G.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).map
        (F.mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (G.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  have := exact_isLeftDerivedFunctor (F := F)
  have := exact_postcomp_isLeftDerivedFunctor (F := F) (G := G) R η hη hR
  have := G.rightDerivedFunctorOfKInjectiveReplacement_postcomp_isRightDerivedFunctor
    R η hη hR F.mapDerivedCategory
  exact (adj.mapHomologicalComplex (.up ℤ)).derivedη_fac_app
    (HomologicalComplex.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactors.hom
    (G.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR) K

/-- The derived counit is induced by the original degreewise adjunction counit. -/
@[reassoc]
lemma rightDerivedAdjunctionOfKInjectiveReplacement_counit_app (I : CochainComplex D ℤ) :
    F.mapDerivedCategory.map
        ((G.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app I) ≫
      (adj.rightDerivedAdjunctionOfKInjectiveReplacement R η hη hR).counit.app
        (DerivedCategory.Q.obj I) =
    F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have := exact_isLeftDerivedFunctor (F := F)
  have := exact_postcomp_isLeftDerivedFunctor (F := F) (G := G) R η hη hR
  have := G.rightDerivedFunctorOfKInjectiveReplacement_postcomp_isRightDerivedFunctor
    R η hη hR F.mapDerivedCategory
  exact (adj.mapHomologicalComplex (.up ℤ)).derivedε_fac_app
    (HomologicalComplex.quasiIso D (.up ℤ)) F.mapDerivedCategoryFactors.hom
    (G.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR) I

end CategoryTheory.Adjunction
