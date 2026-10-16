/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

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
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom X α M n
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let e₀ := moduleSpecΓFunctor.mapIso (moduleHigherDirectImageAffineIso f M I n)
  let e₁ := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app (C.homology (n : ℤ))
  let e₂ := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex)
  exact e₀.toLinearEquiv.trans (e₁.symm.toLinearEquiv.trans
    (e₂.toLinearEquiv.trans (moduleResolutionSectionsCohomologyLinearEquiv X α I n)))

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

/-- Use the installed standard derived categories of the actual module sheaves. -/
local instance affineHigherImageCohomologyStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

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
  (moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.pushforward f).rightDerivedSingleHomologyIso n).app M).symm).toLinearEquiv
    |>.trans (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n)

/-- The native derived-single homology sheaves over an affine target are quasicoherent. -/
theorem moduleDerivedPushforwardSingleAffineHomology_isQuasicoherent (n : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).rightDerivedSingleHomologyIso n).app M)
    (moduleHigherDirectImageAffine_isQuasicoherent f M n)

end AlgebraicGeometry.Scheme.Cohomology
