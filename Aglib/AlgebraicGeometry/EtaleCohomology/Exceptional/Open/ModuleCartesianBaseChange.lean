/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIsomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original module lower-shriek base change on a genuine Cartesian square

The canonical comparison with the native pullback transports the actual
right-adjoint exchange. The only cancellation is the original native
pullback unit along that scheme isomorphism. Taking its adjunction mate
therefore retains the specified native adjunction maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]

/-- Actual inverse-image transport through the canonical Cartesian comparison. -/
def moduleCartesianInverseImageIso :
    moduleInverseImage i Λ ≅
      moduleInverseImage (pullback.snd j f) Λ ⋙ moduleInverseImage h.isoPullback.hom Λ :=
  eqToIso (congrArg (fun a => moduleInverseImage a Λ) h.isoPullback_hom_snd.symm) ≪≫
    moduleInverseImageCompIso Λ (pullback.snd j f) h.isoPullback.hom

/-- Actual direct-image transport through the same canonical Cartesian comparison. -/
def moduleCartesianDirectImageIso :
    moduleDirectImage g Λ ≅
      moduleDirectImage h.isoPullback.hom Λ ⋙ moduleDirectImage (pullback.fst j f) Λ :=
  eqToIso (congrArg (fun a => moduleDirectImage a Λ) h.isoPullback_hom_fst.symm) ≪≫
    moduleDirectImageCompIso Λ (pullback.fst j f) h.isoPullback.hom

/-- The Cartesian right composite reduces by the original unit along the canonical source iso. -/
def moduleCartesianRightIso :
    moduleInverseImage i Λ ⋙ moduleDirectImage g Λ ≅
      moduleInverseImage (pullback.snd j f) Λ ⋙ moduleDirectImage (pullback.fst j f) Λ :=
  Functor.isoWhiskerRight (moduleCartesianInverseImageIso g i j f h Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (moduleCartesianDirectImageIso g i j f h Λ) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (moduleInverseImageUnitIsoOfIso Λ h.isoPullback).symm _ ≪≫
        Functor.leftUnitor _)

/-- The native right-adjoint exchange for the given, not renamed, Cartesian square. -/
def moduleCartesianExchangeIso :
    moduleDirectImage f Λ ⋙ moduleInverseImage j Λ ≅
      moduleInverseImage i Λ ⋙ moduleDirectImage g Λ :=
  moduleEtaleBaseChangeIso f j Λ ≪≫ (moduleCartesianRightIso g i j f h Λ).symm

/-- Arbitrary Cartesian base change for genuine native module lower shriek. -/
def moduleLowerShriekCartesianBaseChangeIso :
    moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ ≅
      moduleInverseImage g Λ ⋙ moduleLowerShriek i Λ :=
  (((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).ofNatIsoRight
    (moduleCartesianExchangeIso g i j f h Λ)).leftAdjointUniq
      ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ))

/-- The Cartesian comparison is the mate of the transported original right exchange. -/
@[reassoc]
theorem moduleLowerShriekCartesianBaseChangeIso_homEquiv (M : ModuleSheaf U Λ) :
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).homEquiv _ _
        ((moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).hom.app M) ≫
      (moduleCartesianExchangeIso g i j f h Λ).hom.app
        ((moduleLowerShriek i Λ).obj ((moduleInverseImage g Λ).obj M)) =
    ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ)).unit.app M := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply,
    moduleLowerShriekCartesianBaseChangeIso, Functor.comp_obj] using
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).ofNatIsoRight
        (moduleCartesianExchangeIso g i j f h Λ))
      ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ)) M

/-- The Cartesian comparison retains the exact original composite adjunction unit. -/
@[reassoc]
theorem moduleLowerShriekCartesianBaseChangeIso_unit (M : ModuleSheaf U Λ) :
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).unit.app M ≫
      (moduleInverseImage j Λ).map ((moduleDirectImage f Λ).map
        ((moduleLowerShriekCartesianBaseChangeIso g i j f h Λ).hom.app M)) ≫
      (moduleCartesianExchangeIso g i j f h Λ).hom.app
        ((moduleLowerShriek i Λ).obj ((moduleInverseImage g Λ).obj M)) =
    ((moduleInverseImageAdjunction g Λ).comp (moduleLowerShriekAdjunction i Λ)).unit.app M := by
  simpa only [Adjunction.homEquiv_unit, Functor.comp_map, Category.assoc] using
    moduleLowerShriekCartesianBaseChangeIso_homEquiv g i j f h Λ M

/-- For a Cartesian square over the same open source, base change gives its original extension. -/
def moduleLowerShriekCartesianIdentityIso
    {U Y X : Scheme.{u}} (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
    [Etale i] [Etale j] (h : IsPullback (𝟙 U) i j f) (Λ : Type (u + 1)) [Ring Λ] :
    moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ ≅ moduleLowerShriek i Λ :=
  moduleLowerShriekCartesianBaseChangeIso (𝟙 U) i j f h Λ ≪≫
    Functor.isoWhiskerRight (moduleInverseImageIdIso Λ U) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.EtaleCohomology
