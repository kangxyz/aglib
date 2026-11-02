/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExactCoefficients

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Exact restriction of abelian sheaves to a slice site

The functor is the original `J.overPullback AddCommGrpCat U`. Limits are
computed on the underlying presheaves. Epimorphisms are preserved because
`Over.forget U` is cocontinuous and hence preserves local surjectivity under
precomposition. No fullness of `Over.forget U`, enough-points assumption,
or unproved preservation of injectives is used.

Site, morphism and coefficient universes are independent. Sheafification
and the concrete locally-bijective description remain explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.SliceCohomology

universe u v m w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

/-- Actual slice restriction is additive on its original maps. -/
instance overPullback_additive : (J.overPullback AddCommGrpCat.{m} U).Additive :=
  GrothendieckTopology.overPullback_additive J AddCommGrpCat.{m} U

/-- Restriction preserves every limit whose shape is admitted by the coefficient category. -/
instance overPullback_preservesLimitsOfShape {K : Type w} [Category.{w'} K]
    [HasLimitsOfShape K AddCommGrpCat.{m}] :
    PreservesLimitsOfShape K (J.overPullback AddCommGrpCat.{m} U) :=
  GrothendieckTopology.overPullback_preservesLimitsOfShape J AddCommGrpCat.{m} U

/-- The literal restriction functor preserves finite limits. -/
instance overPullback_preservesFiniteLimits :
    PreservesFiniteLimits (J.overPullback AddCommGrpCat.{m} U) :=
  GrothendieckTopology.overPullback_preservesFiniteLimits J AddCommGrpCat.{m} U

variable [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [J.HasSheafCompose (forget AddCommGrpCat.{m})]
  [HasSheafify (J.over U) AddCommGrpCat.{m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{m})]

/-- Cocontinuity of the original slice projection preserves local surjectivity,
and therefore epimorphisms of abelian sheaves. -/
instance overPullback_preservesEpimorphisms :
    (J.overPullback AddCommGrpCat.{m} U).PreservesEpimorphisms where
  preserves f hf :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{m}
      ((J.overPullback AddCommGrpCat.{m} U).map f)).mp
        (GrothendieckTopology.overPullback_map_isLocallySurjective
          J AddCommGrpCat.{m} U f hf)

/-- Exactness of restriction follows from kernels and the actual local lifting of epis. -/
instance overPullback_preservesHomology :
    (J.overPullback AddCommGrpCat.{m} U).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The original restriction functor also preserves finite colimits. -/
instance overPullback_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{m} U) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end CategoryTheory.Sheaf.SliceCohomology
