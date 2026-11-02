/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.CounitNaturality

/-!
# Original affine higher-image comparison and coefficient naturality

The actual counit homology comparison is natural for the original complex
maps. Native resolution lifts therefore give the original coefficient map
under the affine higher-image and cohomology comparisons. All objects and
structural actions remain the original ones.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u w

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (I : InjectiveResolution M) (J : InjectiveResolution N)
  {v : M ⟶ N} (φ : InjectiveResolution.Hom I J v)

attribute [local instance] affineCoefficientDerived

/-- Naturality of the original comparison, using its original counit witness. -/
@[reassoc]
theorem moduleHigherDirectImageAffineIso_hom_naturality (n : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived n).map v ≫
        (moduleHigherDirectImageAffineIso f N J n).hom =
      (moduleHigherDirectImageAffineIso f M I n).hom ≫
        (tilde.functor (CommRingCat.of R)).map
          (homologyMap ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map
            (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map φ.hom'))
              (n : ℤ)) :=
  moduleHigherDirectImageAffineIso_hom_naturality_of_counit_quasiIso f I J
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I)
    (moduleResolutionPushforwardTildeCounit_quasiIso f N J) φ n

/-- Naturality of the original comparison, using its original counit witness. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_naturality (n : ℕ)
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f N J n
        (moduleSpecΓFunctor.map (((Scheme.Modules.pushforward f).rightDerived n).map v) x) =
      moduleCohomologyMapOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) v n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x) :=
  moduleHigherDirectImageAffineSectionsLinearEquiv_naturality_of_counit_quasiIso f I J
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I)
    (moduleResolutionPushforwardTildeCounit_quasiIso f N J) n x

/-- Naturality of the original comparison, using its original counit witness. -/
theorem moduleDerivedPushforwardSingleAffineSectionsLinearEquiv_naturality (n : ℕ)
    (x : moduleSpecΓFunctor.obj
      ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)))) :
    moduleDerivedPushforwardSingleAffineSectionsLinearEquiv f N J n
        (moduleSpecΓFunctor.map
          ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).map
            ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map
              ((DerivedCategory.Plus.singleFunctor X.Modules 0).map v))) x) =
      moduleCohomologyMapOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) v n
        (moduleDerivedPushforwardSingleAffineSectionsLinearEquiv f M I n x) :=
  moduleDerivedPushforwardSingleAffineSectionsLinearEquiv_naturality_of_counit_quasiIso f I J
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I)
    (moduleResolutionPushforwardTildeCounit_quasiIso f N J) n x

end AlgebraicGeometry.Scheme.Cohomology
