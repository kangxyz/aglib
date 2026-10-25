/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChangeResolution
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionCycles

/-! # Original higher exchange on actual cycle sections

The actual pullback of sections followed by the original higher exchange is
computed by the actual inverse-image cycle comparison and the native lifted
resolution map. All four derived-category models remain independent. No
base-change isomorphism or cohomological exactness of global sections is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original higher exchange preserves the actual cycle-section formula
under the native resolution and terminal comparisons. -/
theorem higherBaseChangeMap_cycle_sections {F : AbelianSheaf.{u, u + 1} X}
    (I : InjectiveResolution F) (J : InjectiveResolution ((inverseImage g').obj F)) (q : ℕ) :
    let K := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := ((directImage f').mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let φ := InjectiveResolution.ExactFunctor.liftPlus (inverseImage g') I J (𝟙 _)
    let ψ := ((Functor.exchangeOnComplexes
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h)).app I.cochainComplexPlus ≫
        (directImage f').mapCochainComplexPlus.map φ).hom
    (globalSections S).map (K.homologyπ (q : ℤ)) ≫
        (globalSections S).map (I.isoRightDerivedObjCochain (directImage f) q).inv ≫
        globalSectionsPullback g ((higherDirectImage f q).obj F) ≫
        (globalSections S').map ((higherBaseChangeMap f f' g g' h q).app F) ≫
        (globalSections S').map (J.isoRightDerivedObjCochain (directImage f') q).hom =
      globalSectionsPullback g (K.cycles (q : ℤ)) ≫
        (globalSections S').map (((K.sc (q : ℤ)).mapCyclesIso (inverseImage g)).inv ≫
          cyclesMap ψ (q : ℤ) ≫ T.homologyπ (q : ℤ)) := by
  dsimp only
  have hc := Functor.higherResolutionExchangeEquation_cycles
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) I J
    (InjectiveResolution.ExactFunctor.liftPlus (inverseImage g') I J (𝟙 _)) q
    ((higherBaseChangeMap f f' g g' h q).app F)
    (higherBaseChangeMap_resolution_lift f f' g g' h I J q)
  have hs := congrArg (globalSections S').map hc
  simp only [CategoryTheory.Functor.map_comp] at hs
  rw [reassoc_of% globalSectionsPullback_naturality g
      (I.isoRightDerivedObjCochain (directImage f) q).inv,
    reassoc_of% globalSectionsPullback_naturality g
      ((((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ
        (q : ℤ))]
  rw [hs, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
