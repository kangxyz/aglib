/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Basic
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Replacement

/-!
# Actual unbounded right-derived functors from Grothendieck categories

The constructed regular-stage K-injective replacement is used with the native
chosen separator. Every additive functor out of a Grothendieck abelian category
therefore has an unbounded right-derived functor on the existing derived
categories. This leaf assumes no replacement functor or replacement-existence
class. The original natural augmentation computes the universal derived unit.
-/

@[expose] public noncomputable section

universe s u v w u' v' w'

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- Actual pointwise derived existence, supplied by the proved regular-stage
 K-injective replacement rather than a replacement-existence assumption. -/
instance hasPointwiseRightDerivedFunctor_of_isGrothendieckAbelian :
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseRightDerivedFunctor
      (HomologicalComplex.quasiIso C (.up ℤ)) :=
  CochainComplex.hasPointwiseRightDerivedFunctor_of_kInjectiveReplacement
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C)) F

variable [HasDerivedCategory.{w} C]

/-- The actual unbounded right-derived functor of an additive functor with
 Grothendieck abelian source, on the native derived categories. -/
abbrev unboundedRightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D :=
  F.rightDerivedFunctorOfKInjectiveReplacement
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C))

/-- The original universal localization unit of the actual unbounded functor. -/
abbrev unboundedRightDerivedFunctorUnit :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.unboundedRightDerivedFunctor :=
  F.rightDerivedFunctorOfKInjectiveReplacementUnit
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C))

/-- Computation by any supplied K-injective resolution, retaining its original map. -/
abbrev unboundedRightDerivedFunctorObjIso
    {K I : CochainComplex C ℤ} (i : K ⟶ I) [QuasiIso i] [I.IsKInjective] :
    F.unboundedRightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
  F.rightDerivedFunctorOfKInjectiveReplacementObjIso
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C)) i

/-- The computation comparison identifies the universal unit with the image
 of the specified original K-injective resolution map. -/
@[reassoc]
lemma unboundedRightDerivedFunctorUnit_app_comp_objIso_hom
    {K I : CochainComplex C ℤ} (i : K ⟶ I) [QuasiIso i] [I.IsKInjective] :
    F.unboundedRightDerivedFunctorUnit.app K ≫
      (F.unboundedRightDerivedFunctorObjIso i).hom =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i) :=
  F.rightDerivedFunctorOfKInjectiveReplacementUnit_app_comp_objIso_hom _ _ _ _ i

/-- The actual regular-stage model computes the unbounded derived value. -/
abbrev unboundedRightDerivedFunctorReplacementIso (K : CochainComplex C ℤ) :
    F.unboundedRightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C)).obj K)) :=
  F.unboundedRightDerivedFunctorObjIso
    ((CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C)).app K)

/-- The actual tower augmentation, not a chosen unrelated map, represents
 the universal unbounded derived comparison. -/
@[reassoc]
lemma unboundedRightDerivedFunctorUnit_app_comp_replacementIso_hom (K : CochainComplex C ℤ) :
    F.unboundedRightDerivedFunctorUnit.app K ≫
      (F.unboundedRightDerivedFunctorReplacementIso K).hom =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C)).app K)) :=
  F.unboundedRightDerivedFunctorUnit_app_comp_objIso_hom _

end CategoryTheory.Functor
