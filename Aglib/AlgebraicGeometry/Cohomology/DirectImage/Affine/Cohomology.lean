/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SectionsCounit
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.SectionsCounitHomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.CounitDegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.CounitNaturality
public import Aglib.CategoryTheory.Abelian.Injective.ExtZero
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact

/-!
# Actual affine higher-image sections and unchanged cohomology

The actual higher direct image over a spectrum has the original cohomology
module as its sections, with the specified structural action. The comparison
uses the original counit computation, original tilde unit and actual section
complex of the supplied native module injective resolution. The installed
bounded-below derived functor at the original single has the same canonical
comparison through the native higher-derived/homology isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Actual affine sections of the original higher direct image are unchanged original
cohomology, with its actual structural ring action and original resolution classes. -/
def moduleHigherDirectImageAffineSectionsLinearEquiv (I : InjectiveResolution M) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  moduleHigherDirectImageAffineSectionsLinearEquiv_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) n

/-- Every original factor and the original section-resolution class remain in the forward map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_apply
    (I : InjectiveResolution M) (n : ℕ)
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x =
      moduleResolutionSectionsCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso
          f (.up ℤ) I.cochainComplex).hom (n : ℤ)
          ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app
            (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
              (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
                I.cochainComplex)).homology (n : ℤ))
            (moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom x))) := rfl

/- Use the installed standard derived categories of the actual module sheaves. -/
attribute [local instance] affineHigherImageCohomologyStandard

/-- Original affine sections of homology of the installed derived direct image at the actual
single are the unchanged original cohomology module. -/
def moduleDerivedPushforwardSingleAffineSectionsLinearEquiv
    (I : InjectiveResolution M) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj
      ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  moduleDerivedPushforwardSingleAffineSectionsLinearEquiv_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) n

/-- The native derived-single homology sheaves over an affine target are quasicoherent. -/
theorem moduleDerivedPushforwardSingleAffineHomology_isQuasicoherent (n : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).rightDerivedSingleHomologyIso n).app M)
    (moduleHigherDirectImageAffine_isQuasicoherent f M n)

/-- The unchanged first two affine cohomology factors, from actual higher-image sections
to homology of the original section complex of the supplied resolution. -/
def moduleHigherDirectImageAffineSectionsHomologyMap (I : InjectiveResolution M) (n : ℕ) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) n

/-- The original affine section/homology factor is invertible. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_isIso
    (I : InjectiveResolution M) (n : ℕ) :
    IsIso (moduleHigherDirectImageAffineSectionsHomologyMap f M I n) :=
  moduleHigherDirectImageAffineSectionsHomologyMap_isIso_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) n

/-- The unchanged affine factor retains the native homology counit mate and the original
integer-resolution comparison. Global sections need not preserve homology. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_counit
    (I : InjectiveResolution M) (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let : (tilde.functor (CommRingCat.of R)).Additive := by
      let : PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
        Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
      exact CategoryTheory.Functor.additive_of_preserves_binary_products _
    let : (tilde.functor (CommRingCat.of R)).PreservesHomology :=
      Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
    let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Additive :=
      Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
    moduleHigherDirectImageAffineSectionsHomologyMap f M I n ≫
        (tilde.adjunction (R := CommRingCat.of R)).homologyCounitMate (K.sc (n : ℤ)) =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  exact moduleHigherDirectImageAffineSectionsHomologyMap_counit_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) n

/-- In degree zero, the original higher-image section comparison recovers the original
pushforward global section through the native right-derived-zero map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero
    (I : InjectiveResolution M)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj M)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    moduleH0EquivOfHom X α M
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I 0
          (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward f).toRightDerivedZero.app M) x)) =
      (moduleSpecPushforwardGlobalSectionsIso f).hom.app M x :=
  moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero_of_counit_quasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I) x

end AlgebraicGeometry.Scheme.Cohomology
