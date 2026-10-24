/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Grothendieck
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.PlusComparison
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Triangulated

/-!
# Actual unbounded derived adjunction and bounded-below comparison

These interfaces specialize the generic derived comparisons to the constructed
regular-stage replacement. No replacement data are assumed. Triangulatedness
is inherited from the proved generic instance through the definition of the
actual unbounded functor. All comparison equations use its original unit.
-/

@[expose] public noncomputable section

universe s u v w u' v' w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- The canonical bounded-below comparison for the actual unbounded functor. -/
abbrev unboundedRightDerivedFunctorPlusIso :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.unboundedRightDerivedFunctor :=
  F.rightDerivedFunctorOfKInjectiveReplacementPlusIso
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator C))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator C))

/-- The actual bounded-below comparison preserves the original localization units. -/
@[reassoc]
lemma unboundedRightDerivedFunctorPlusIso_unit_app (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      F.unboundedRightDerivedFunctorPlusIso.hom.app (DerivedCategory.Plus.Q.obj K) =
        F.unboundedRightDerivedFunctorUnit.app K.obj :=
  F.rightDerivedFunctorOfKInjectiveReplacementPlusIso_unit_app _ _ _ _ K

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [IsGrothendieckAbelian.{s} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The actual unbounded right-derived adjunction for an exact left adjoint.
 The right-adjoint source is Grothendieck; no replacement data are supplied. -/
abbrev unboundedRightDerivedAdjunction : F.mapDerivedCategory ⊣ G.unboundedRightDerivedFunctor :=
  adj.rightDerivedAdjunctionOfKInjectiveReplacement
    (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator D))
    (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator D))
    (CochainComplex.kInjectiveReplacementUnit_quasiIso (isSeparator_separator D))
    (CochainComplex.kInjectiveReplacement_isKInjective (isSeparator_separator D))

/-- The actual derived unit retains the original cochain adjunction unit. -/
@[reassoc]
lemma unboundedRightDerivedAdjunction_unit_app (K : CochainComplex C ℤ) :
    adj.unboundedRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
      G.unboundedRightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      G.unboundedRightDerivedFunctorUnit.app ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  adj.rightDerivedAdjunctionOfKInjectiveReplacement_unit_app _ _ _ _ K

/-- The actual derived counit retains the original cochain adjunction counit. -/
@[reassoc]
lemma unboundedRightDerivedAdjunction_counit_app (I : CochainComplex D ℤ) :
    F.mapDerivedCategory.map (G.unboundedRightDerivedFunctorUnit.app I) ≫
      adj.unboundedRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
    F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) :=
  adj.rightDerivedAdjunctionOfKInjectiveReplacement_counit_app _ _ _ _ I

end CategoryTheory.Adjunction
