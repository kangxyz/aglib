/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ComplexSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChangeResolution
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition

/-! # Actual exchange resolution maps on section complexes

The complex map computing the original exchange retains the original pullback
of global sections on the total spaces, in every integer degree. The target
resolution map is an actual map of complexes, not a cohomological premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
  (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)

/-- The original termwise exchange, followed by any actual lift, induces the
original global-section complex pullback under native terminal transports. -/
theorem baseChangeMap_resolution_sections
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X))
    (L : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X'))
    (φ : (inverseImage g').mapCochainComplexPlus.obj K ⟶ L) :
    globalSectionsPullbackComplex g ((directImage f).mapCochainComplexPlus.obj K) ≫
        (globalSections S').mapCochainComplexPlus.map
          ((Functor.exchangeOnComplexes
            (directImage f) (directImage f') (inverseImage g) (inverseImage g')
            (baseChangeMap f f' g g' h)).app K ≫
              (directImage f').mapCochainComplexPlus.map φ) ≫
        (NatIso.mapCochainComplexPlus (directImageGlobalSectionsIso f')).hom.app L =
      (NatIso.mapCochainComplexPlus (directImageGlobalSectionsIso f)).hom.app K ≫
        globalSectionsPullbackComplex g' K ≫
        (globalSections X').mapCochainComplexPlus.map φ := by
  exact Functor.exchangeOnComplexes_sections
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (globalSections S) (globalSections X) (globalSections S') (globalSections X')
    (baseChangeMap f f' g g' h)
    (directImageGlobalSectionsIso f) (directImageGlobalSectionsIso f')
    (globalSectionsPullback g) (globalSectionsPullback g')
    (baseChangeMap_globalSections f f' g g' h) K L φ
    (globalSectionsPullbackComplex g ((directImage f).mapCochainComplexPlus.obj K))
    (globalSectionsPullbackComplex g' K)
    (globalSectionsPullbackComplex_f g ((directImage f).mapCochainComplexPlus.obj K))
    (globalSectionsPullbackComplex_f g' K)

end AlgebraicGeometry.Scheme.EtaleCohomology
