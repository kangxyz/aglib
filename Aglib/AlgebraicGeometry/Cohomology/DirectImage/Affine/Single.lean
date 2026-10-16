/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle

/-!
# Actual affine derived direct image of a quasicoherent single

The installed right-derived pushforward of a quasicoherent coefficient
under an affine morphism is its original ordinary pushforward in degree
zero. The isomorphism is the sole coefficient-specific acyclic-single
comparison, with its original unit and coefficient maps. No exactness
claim for pushforward on all module sheaves is made.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The installed standard ambient derived category of actual module sheaves. -/
local instance affineSingleStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Affine quasicoherent acyclicity makes the original installed derived unit
invertible on this coefficient's native degree-zero single. -/
theorem isIso_derivedPushforwardPlusUnit_single_of_isAffineHom :
    IsIso ((derivedPushforwardPlusUnit f).app
      ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) :=
  (pushforward f).isIso_rightDerivedFunctorPlusUnit_single_of_isZero_rightDerived_succ M
    (isZero_rightDerived_pushforward_succ f M)

/-- The actual affine derived image of a quasicoherent coefficient is the original
ordinary pushforward placed in degree zero. -/
def affineDerivedPushforwardSingleIso :
    (derivedPushforwardPlus f).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pushforward f).obj M) :=
  (pushforward f).rightDerivedFunctorPlusSingleIsoOfAcyclic M
    (isZero_rightDerived_pushforward_succ f M)

/-- This is the original derived-unit comparison, retaining the native
single-complex map of the ordinary pushforward. -/
@[reassoc]
theorem affineDerivedPushforwardSingleIso_unit :
    (derivedPushforwardPlusUnit f).app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (affineDerivedPushforwardSingleIso f M).hom =
      DerivedCategory.Plus.Q.map
        (show (pushforward f).mapCochainComplexPlus.obj
            ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ⟶
            (CochainComplex.singleFunctorPlus Y.Modules 0).obj ((pushforward f).obj M) from
          ObjectProperty.homMk
            ((HomologicalComplex.singleMapHomologicalComplex
              (pushforward f) (.up ℤ) 0).hom.app M)) :=
  (pushforward f).rightDerivedFunctorPlusSingleIsoOfAcyclic_unit M
    (isZero_rightDerived_pushforward_succ f M)

/-- The comparison preserves every original quasicoherent coefficient arrow. -/
@[reassoc]
theorem affineDerivedPushforwardSingleIso_hom_naturality
    {N : X.Modules} [N.IsQuasicoherent] (g : M ⟶ N) :
    (derivedPushforwardPlus f).map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g) ≫
        (affineDerivedPushforwardSingleIso f N).hom =
      (affineDerivedPushforwardSingleIso f M).hom ≫
        (DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((pushforward f).map g) :=
  (pushforward f).rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality g
    (isZero_rightDerived_pushforward_succ f M) (isZero_rightDerived_pushforward_succ f N)

/-- The native affine derived single is concentrated in degree zero. -/
theorem affineDerivedPushforwardSingle_bounds :
    ((derivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)).IsGE 0 ∧
      ((derivedPushforwardPlus f).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)).IsLE 0 :=
  ⟨DerivedCategory.Plus.TStructure.t.isGE_of_iso (affineDerivedPushforwardSingleIso f M).symm 0,
    DerivedCategory.Plus.TStructure.t.isLE_of_iso (affineDerivedPushforwardSingleIso f M).symm 0⟩

end AlgebraicGeometry.Scheme.Modules
