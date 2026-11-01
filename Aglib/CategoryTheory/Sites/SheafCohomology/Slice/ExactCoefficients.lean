/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Continuous.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Exact restriction to a slice with native abelian coefficients

The original slice pullback preserves limits on presheaves. Cocontinuity
preserves the actual local lifts characterizing epimorphisms, giving exactness
for concrete abelian coefficients with the stated native sheafification data.
No new sheaf category, pullback, or coefficient realization is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory

universe c h a b s t w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (A : Type a) [Category.{b} A] (U : C)

/-- Original slice restriction is additive on the original component maps. -/
instance (priority := 100) overPullback_additive [Preadditive A] :
    (J.overPullback A U).Additive where
  map_add := by intros; rfl

/-- Original slice restriction preserves each limit shape admitted by the coefficients. -/
instance (priority := 100) overPullback_preservesLimitsOfShape {K : Type s} [Category.{t} K]
    [HasLimitsOfShape K A] : PreservesLimitsOfShape K (J.overPullback A U) :=
  Functor.sheafPushforwardContinuous_preservesLimitsOfShape (Over.forget U) A (J.over U) J

/-- Original slice restriction preserves finite limits. -/
instance (priority := 100) overPullback_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (J.overPullback A U) := ⟨fun _ => inferInstance⟩

variable [Abelian A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [HasSheafify J A] [J.WEqualsLocallyBijective A]
  [J.HasSheafCompose (forget A)]

include FA CA

/-- An original epimorphism has the same local lifts after restriction to the slice. -/
theorem overPullback_map_isLocallySurjective {F G : Sheaf J A} (f : F ⟶ G) (hf : Epi f) :
    Sheaf.IsLocallySurjective ((J.overPullback A U).map f) := by
  let : Sheaf.IsLocallySurjective f := (Sheaf.isLocallySurjective_iff_epi' A f).mpr hf
  change Presheaf.IsLocallySurjective (J.over U)
    (Functor.whiskerLeft (Over.forget U).op f.hom)
  exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) f.hom

variable [(J.over U).HasSheafCompose (forget A)]

/-- Cocontinuity carries original local lifts of an epimorphism to the slice. -/
theorem overPullback_preservesEpimorphisms :
    (J.overPullback A U).PreservesEpimorphisms where
  preserves {F G} f hf := by
    let : Sheaf.IsLocallySurjective ((J.overPullback A U).map f) :=
      overPullback_map_isLocallySurjective J A U f hf
    exact Sheaf.epi_of_isLocallySurjective _

variable [HasSheafify (J.over U) A]

/-- Original slice restriction is exact by preservation of kernels and epimorphisms. -/
theorem overPullback_preservesHomology :
    (J.overPullback A U).PreservesHomology := by
  let : (J.overPullback A U).PreservesEpimorphisms :=
    overPullback_preservesEpimorphisms J A U
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Original slice restriction consequently preserves finite colimits. -/
theorem overPullback_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback A U) := by
  let : (J.overPullback A U).PreservesHomology := overPullback_preservesHomology J A U
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end CategoryTheory.GrothendieckTopology
