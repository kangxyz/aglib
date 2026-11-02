/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ComplexSectionChase
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCycleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChangeCycleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChangeResolutionSections

/-! # Original higher exchange and original global cohomology pullback

The original higher base-change map on global higher-image sections commutes
with the original Ext cohomology pullback. The proof compares actual cycle
sections in the native resolutions, using their original term inclusions.
Source and target Ext universes remain independent. The ordinary formula has no
derived-category parameter. No properness, Cartesian hypothesis or base-change
isomorphism is needed for this equality of the original maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The actual higher base-change map takes the original global higher-image
section to the section of the original pulled-back Ext class, in every degree. -/
theorem higherBaseChangeMap_cohomologyToHigherSections
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (x : Sheaf.H.{w} F q) :
    (globalSections S').map ((higherBaseChangeMap f f' g g' h q).app F)
        (globalSectionsPullback g ((higherDirectImage f q).obj F)
          (cohomologyToHigherSections f F q x)) =
      cohomologyToHigherSections f' ((inverseImage g').obj F) q
        (cohomologyPullback.{u, w, w'} g' F q x) := by
  let I := injectiveResolution F
  let J := injectiveResolution ((inverseImage g').obj F)
  obtain ⟨z, z', hz, hz', ht⟩ :=
    cohomologyToHigherSections_pullback_cycles f f' g' I J q x
  exact Functor.exchangeOnComplexes_section_chase
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (globalSections S) (globalSections X) (globalSections S') (globalSections X')
    (baseChangeMap f f' g g' h)
    (directImageGlobalSectionsIso f) (directImageGlobalSectionsIso f')
    (globalSectionsPullbackNatTrans g) (globalSectionsPullbackNatTrans g')
    I.cochainComplexPlus J.cochainComplexPlus
    (InjectiveResolution.ExactFunctor.liftPlus (inverseImage g') I J (𝟙 _)) (q : ℤ)
    (I.isoRightDerivedObjCochain (directImage f) q)
    (J.isoRightDerivedObjCochain (directImage f') q)
    ((higherBaseChangeMap f f' g g' h q).app F)
    (globalSectionsPullbackComplex g
      ((directImage f).mapCochainComplexPlus.obj I.cochainComplexPlus))
    (globalSectionsPullbackComplex g' I.cochainComplexPlus)
    (globalSectionsPullbackComplex_f g
      ((directImage f).mapCochainComplexPlus.obj I.cochainComplexPlus) (q : ℤ))
    (globalSectionsPullbackComplex_f g' I.cochainComplexPlus (q : ℤ))
    (baseChangeMap_resolution_sections f f' g g' h I.cochainComplexPlus
      J.cochainComplexPlus
      (InjectiveResolution.ExactFunctor.liftPlus (inverseImage g') I J (𝟙 _)))
    (higherBaseChangeMap_cycle_sections f f' g g' h I J q)
    (cohomologyToHigherSections f F q x)
    (cohomologyToHigherSections f' ((inverseImage g').obj F) q
      (cohomologyPullback.{u, w, w'} g' F q x)) z z' hz hz' ht

end AlgebraicGeometry.Scheme.EtaleCohomology
