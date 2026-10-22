/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Original Spec sections of a pushforward

This is the identity-on-sections comparison with the actual structural ring
map. It supplies coefficient naturality for the ambient formal-functions tower.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {B : CommRingCat.{u}} {Y : Scheme.{u}} (p : Y ⟶ Spec B)

/-- Actual Spec global sections of a pushforward are original upstairs sections. -/
def pushforwardSpecSectionsIso :
    Modules.pushforward p ⋙ moduleSpecΓFunctor ≅
      moduleGlobalSectionsFunctorOfHom Y (p.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom) :=
  NatIso.ofComponents
    (fun M => (modulePushforwardSectionsPresheafIso p (Scheme.ΓSpecIso B).inv.hom M).app
      (op ⊤) ≪≫ moduleTopSectionsIso Y
        (p.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom) M)
    (by intro M N φ; ext x; rfl)

/-- The comparison leaves original section elements unchanged. -/
theorem pushforwardSpecSectionsIso_hom_apply (M : Y.Modules)
    (x : moduleSpecΓFunctor.obj ((Modules.pushforward p).obj M)) :
    (pushforwardSpecSectionsIso p).hom.app M x = x := rfl

/-- The inverse also leaves the original section values unchanged. -/
theorem pushforwardSpecSectionsIso_inv_apply (M : Y.Modules)
    (x : (moduleGlobalSectionsFunctorOfHom Y
      (p.appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom)).obj M) :
    (pushforwardSpecSectionsIso p).inv.app M x = x := rfl

end AlgebraicGeometry.Scheme.Cohomology
