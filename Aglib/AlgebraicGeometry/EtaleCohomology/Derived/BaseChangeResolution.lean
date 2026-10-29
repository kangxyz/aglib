/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionTransport
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorPlus

/-! # The original derived exchange on actual injective resolutions

The original ordinary and derived exchanges satisfy the proved complex-unit
square. Consequently the original derived exchange is computed by termwise
ordinary exchange and any actual augmentation-compatible lift into a target
injective resolution. No base-change isomorphism, properness, smoothness or
cohomological vanishing is assumed. The derived statement retains its selected models;
the ordinary higher formula has no derived-category parameter.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-- The actual original derived exchange equals the actual resolution-complex
map under the installed native resolution comparisons. -/
theorem derivedBaseChangeMap_resolution {F : AbelianSheaf.{u, u + 1} X}
    (I : InjectiveResolution F) (J : InjectiveResolution ((inverseImage g').obj F))
    (φ : (inverseImage g').mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      J.cochainComplexPlus)
    (hφ : (inverseImage g').mapCochainComplexPlus.map I.ιPlus ≫ φ =
      (show (inverseImage g').mapCochainComplexPlus.obj
            ((CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X) 0).obj F) ⟶
          (CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X') 0).obj
            ((inverseImage g').obj F) from
        ObjectProperty.homMk
          ((singleMapHomologicalComplex (inverseImage g') (.up ℤ) 0).hom.app F)) ≫
        J.ιPlus) :
    Functor.ResolutionExchangeEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) I J φ :=
  Functor.resolutionExchangeEquation_of_actualUnit
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) I J φ
    (derivedBaseChangeMap_actualUnit f f' g g' h) hφ

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original higher exchange is the homology map of the actual termwise
ordinary exchange followed by the specified resolution lift, in every degree. -/
theorem higherBaseChangeMap_resolution {F : AbelianSheaf.{u, u + 1} X}
    (I : InjectiveResolution F) (J : InjectiveResolution ((inverseImage g').obj F))
    (φ : (inverseImage g').mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      J.cochainComplexPlus)
    (hφ : (inverseImage g').mapCochainComplexPlus.map I.ιPlus ≫ φ =
      (show (inverseImage g').mapCochainComplexPlus.obj
            ((CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X) 0).obj F) ⟶
          (CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} X') 0).obj
            ((inverseImage g').obj F) from
        ObjectProperty.homMk
          ((singleMapHomologicalComplex (inverseImage g') (.up ℤ) 0).hom.app F)) ≫
        J.ιPlus) (q : ℕ) :
    Functor.HigherResolutionExchangeEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) I J φ q
      ((higherBaseChangeMap f f' g g' h q).app F) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  exact Functor.higherResolutionExchangeEquation_of_actualTransport
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) I J φ q
    (higherDirectImageIso f q) (higherDirectImageIso f' q) rfl rfl
    (higherBaseChangeSourceIso f g q).hom (higherBaseChangeTargetIso f' g' q).hom
    (higherBaseChangeMap f f' g g' h q) (higherBaseChangeMap_eq_transport f f' g g' h q)
    (derivedBaseChangeMap_resolution f f' g g' h I J φ hφ)
    (higherBaseChangeMap_app f f' g g' h q F)

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original higher exchange computed using the actual native resolution lift.
The lift and its augmented triangle are constructed, not hypothesized. -/
theorem higherBaseChangeMap_resolution_lift {F : AbelianSheaf.{u, u + 1} X}
    (I : InjectiveResolution F) (J : InjectiveResolution ((inverseImage g').obj F)) (q : ℕ) :
    Functor.HigherResolutionExchangeEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) I J
      (InjectiveResolution.ExactFunctor.liftPlus (inverseImage g') I J (𝟙 _)) q
      ((higherBaseChangeMap f f' g g' h q).app F) := by
  apply higherBaseChangeMap_resolution f f' g g' h I J
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using
    InjectiveResolution.ExactFunctor.liftPlus_augmentation (inverseImage g') I J (𝟙 _)

end AlgebraicGeometry.Scheme.EtaleCohomology
