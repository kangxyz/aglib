/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open.Basic
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde

/-!
# Actual affine-base pushforward sections and original structural sections

The native spectrum section functor of an actual pushforward agrees with
the original sections on the inverse-image open, with their specified
structural action. At the whole space this is the original global-section
functor. The comparisons are the identity on section values and retain
both the actual coefficient complex and its top-to-open restrictions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u w

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- Actual affine-base pushforward sections are the original structural sections on the
inverse-image open. -/
def moduleSpecPushforwardSectionsIso (U : (Spec R).Opens) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.Complex.specSectionsFunctor R U ≅
      moduleOpenSectionsFunctorOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) (f ⁻¹ᵁ U) :=
  NatIso.ofComponents
    (fun M => (modulePushforwardSectionsPresheafIso f (Scheme.ΓSpecIso R).inv.hom M).app (op U))
    (by intro M N φ; ext x; rfl)

theorem moduleSpecPushforwardSectionsIso_hom_app_apply (U : (Spec R).Opens) (M : X.Modules)
    (x : (Scheme.Modules.Complex.specSectionsFunctor R U).obj
      ((Scheme.Modules.pushforward f).obj M)) :
    (moduleSpecPushforwardSectionsIso f U).hom.app M x = x := rfl

/-- Native affine global sections of the actual pushforward are the original structural-ring
global sections on the source. -/
def moduleSpecPushforwardGlobalSectionsIso :
    Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor ≅
      moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) :=
  moduleSpecPushforwardSectionsIso f ⊤ ≪≫
    moduleTopSectionsFunctorIso X (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)

theorem moduleSpecPushforwardGlobalSectionsIso_hom_app_apply (M : X.Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj M)) :
    (moduleSpecPushforwardGlobalSectionsIso f).hom.app M x = x := rfl

theorem moduleSpecPushforwardGlobalSectionsIso_inv_app_apply (M : X.Modules)
    (x : (moduleGlobalSectionsFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).obj M) :
    (moduleSpecPushforwardGlobalSectionsIso f).inv.app M x = x := rfl

variable {ι : Type w} (d : ComplexShape ι) (K : HomologicalComplex X.Modules d)

/-- The original termwise section comparison on an actual coefficient complex. -/
def moduleSpecPushforwardSectionsComplexIso (U : (Spec R).Opens) :
    ((Scheme.Modules.Complex.specSectionsFunctor R U).mapHomologicalComplex d).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K) ≅
      ((moduleOpenSectionsFunctorOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        (f ⁻¹ᵁ U)).mapHomologicalComplex d).obj K :=
  (Functor.mapHomologicalComplexCompIso (moduleSpecPushforwardSectionsIso f U) d).app K

/-- The original native spectrum-global-section complex of the actual pushforward is the
actual structural-ring global-section complex on the source. -/
def moduleSpecPushforwardGlobalSectionsComplexIso :
    (moduleSpecΓFunctor.mapHomologicalComplex d).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K) ≅
      ((moduleGlobalSectionsFunctorOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).mapHomologicalComplex d).obj K :=
  (Functor.mapHomologicalComplexCompIso (moduleSpecPushforwardGlobalSectionsIso f) d).app K

theorem moduleSpecPushforwardGlobalSectionsComplexIso_hom_f_apply (i : ι)
    (x : ((moduleSpecΓFunctor.mapHomologicalComplex d).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K)).X i) :
    (moduleSpecPushforwardGlobalSectionsComplexIso f d K).hom.f i x = x := rfl

/-- The original comparison preserves actual top-to-open section restrictions as an equality
of the original coefficient-complex maps. -/
theorem moduleSpecPushforwardSectionsComplexIso_restriction (U : (Spec R).Opens) :
    Scheme.Modules.Complex.specSectionsComplexRestriction R d U
        (((Scheme.Modules.pushforward f).mapHomologicalComplex d).obj K) ≫
        (moduleSpecPushforwardSectionsComplexIso f d K U).hom =
      (moduleSpecPushforwardSectionsComplexIso f d K ⊤).hom ≫
        (NatTrans.mapHomologicalComplex
          (moduleOpenSectionsRestriction X
            (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
            (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top))) d).app K := by
  ext i x
  rfl

end AlgebraicGeometry.Scheme.Cohomology
