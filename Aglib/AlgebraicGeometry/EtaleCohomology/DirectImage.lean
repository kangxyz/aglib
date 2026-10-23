/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Actual higher direct images on the small étale site

The coefficient universe is the existing value universe `u + 1`. Enough
injectives comes from the Grothendieck abelian sheaf category at that size.
Higher direct images and their bounded-below homology comparisons use the
original direct-image functor and the installed native derived constructions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

/-- The existing large-value small-étale sheaf category has enough injectives.
The essentially-small-site comparison retains the actual sheaf category. -/
instance abelianSheaf_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (AbelianSheaf.{u, u + 1} X) := by
  let : EssentiallySmall.{u + 1} X.Etale := essentiallySmallSelf.{0, u, u + 1} X.Etale
  let : IsGrothendieckAbelian.{u + 1} (AbelianSheaf.{u, u + 1} X) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  infer_instance

instance directImage_isRightAdjoint {X S : Scheme.{u}} (f : X ⟶ S) :
    (directImage f).IsRightAdjoint := (inverseImageAdjunction f).isRightAdjoint

instance directImage_preservesFiniteLimits {X S : Scheme.{u}} (f : X ⟶ S) :
    PreservesFiniteLimits (directImage f) := by infer_instance

instance directImage_additive {X S : Scheme.{u}} (f : X ⟶ S) :
    (directImage f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exact inverse image implies that the original direct image preserves injectives. -/
instance directImage_preservesInjectiveObjects {X S : Scheme.{u}} (f : X ⟶ S) :
    (directImage f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inverseImageAdjunction f)

/-- The actual natural-degree right-derived functor of the existing direct image. -/
abbrev higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) :
    AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S :=
  (directImage f).rightDerived q

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The installed bounded-below derived direct image. -/
abbrev derivedDirectImage (f : X ⟶ S) :
    DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) ⥤
      DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S) :=
  (directImage f).rightDerivedFunctorPlus

/-- Higher direct image is the homology of the actual derived direct image on a single. -/
def higherDirectImageIso (f : X ⟶ S) (q : ℕ) :
    higherDirectImage f q ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        derivedDirectImage f ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ) :=
  (directImage f).rightDerivedSingleHomologyIso q

/-- Degree-zero homology recovers the original direct image with its native normalization. -/
def derivedDirectImageSingleHomologyZeroIso (f : X ⟶ S) :
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
      derivedDirectImage f ⋙
      DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0 ≅ directImage f :=
  (directImage f).rightDerivedSingleHomologyZeroIso

end AlgebraicGeometry.Scheme.EtaleCohomology
