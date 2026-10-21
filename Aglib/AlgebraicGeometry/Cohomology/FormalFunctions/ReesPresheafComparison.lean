/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesLocalRestriction
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesPushforwardSections
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesSections
public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductSectionIso

/-! # The canonical section-presheaf comparison for the geometric Rees image -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

open Modules.Rees

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]

/-- The actual family of ideal-power coefficients, with the original structural scalars. -/
abbrev reesPowerFamily (n : ℕ) : X.Modules :=
  Modules.idealPower X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F I n

local instance reesPowerFamily_isQuasicoherent (n : ℕ) :
    (reesPowerFamily I f F n).IsQuasicoherent :=
  Modules.idealMultiple_isQuasicoherent X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F (I ^ n)

/-- The geometric image pushed back along the affine Rees projection. -/
abbrev reesPushforwardCoefficient : X.Modules :=
  (Modules.pushforward (projection I f)).obj (coefficient I f F)

/-- Actual pushforward sections in the Rees chart coordinates. -/
def reesPushforwardSectionsIso :=
  modulePushforwardSectionsIso (projection I f)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ((structureMap I f).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
    (algebraMap A (reesAlgebra I))
    (moduleSectionsBaseChangeScalars _ _ _ _ Limits.pullback.condition)
    (coefficient I f F)

/-- The affine comparison composes only canonical original section maps. -/
def reesPowerAffineSectionsIso (U : X.affineOpens) :
    (moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (∐ reesPowerFamily I f F)).obj (op U.val) ≅
    (moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPushforwardCoefficient I f F)).obj (op U.val) :=
  moduleAffineSectionsCoproductIso.{u, 0} X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPowerFamily I f F) U.val U.property ≪≫
    (directSumPowerSectionsEquiv I f F U.val U.property).toModuleIso ≪≫
      ((reesPushforwardSectionsIso I f F).app (op U.val)).symm

/-- Each coefficient inclusion has exactly its original homogeneous polynomial value. -/
theorem reesPowerAffineSectionsIso_ι (U : X.affineOpens) (n : ℕ)
    (m : powerSections I f F n U.val) :
    (reesPushforwardSectionsIso I f F).hom.app (op U.val)
      ((reesPowerAffineSectionsIso I f F U).hom
        ((((moduleSectionsPresheafFunctor X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map
          (Sigma.ι (reesPowerFamily I f F) n)).app (op U.val)) m)) =
      homogeneousSectionMap I f F n U.val U.property m := by
  change (reesPushforwardSectionsIso I f F).hom.app (op U.val)
    ((reesPushforwardSectionsIso I f F).inv.app (op U.val)
      (directSumPowerSectionsEquiv I f F U.val U.property
        ((moduleAffineSectionsCoproductIso.{u, 0} X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
          (reesPowerFamily I f F) U.val U.property).hom _))) = _
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app]
  have h := congrArg (fun k => k m)
    (moduleAffineSectionsCoproductIso_ι.{u, 0} X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPowerFamily I f F) U.val U.property n)
  exact congrArg (directSumPowerSectionsEquiv I f F U.val U.property) h

/-- Affine comparison maps commute with original restrictions. -/
theorem reesPowerAffineSectionsIso_naturality {U V : X.affineOpens}
    (i : U.val ⟶ V.val) :
    (moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (∐ reesPowerFamily I f F)).map i.op ≫
        (reesPowerAffineSectionsIso I f F U).hom =
      (reesPowerAffineSectionsIso I f F V).hom ≫
        (moduleSectionsPresheaf X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
          (reesPushforwardCoefficient I f F)).map
          i.op := by
  apply (moduleAffineSectionsCoproductIsColimit.{u, 0} X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (reesPowerFamily I f F) V.val V.property).hom_ext
  intro j
  let n := j.as
  let ι : moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPowerFamily I f F n) ⟶
      moduleSectionsPresheaf X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        (∐ reesPowerFamily I f F) :=
    (moduleSectionsPresheafFunctor X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map
        (Sigma.ι (reesPowerFamily I f F) n)
  change ι.app (op V.val) ≫ _ = ι.app (op V.val) ≫ _
  rw [← Category.assoc, ← ι.naturality]
  ext m
  apply ((reesPushforwardSectionsIso I f F).app (op U.val)).toLinearEquiv.injective
  have hη := (reesPushforwardSectionsIso I f F).hom.naturality
    i.op
  have hm := congrArg (fun k => k ((reesPowerAffineSectionsIso I f F V).hom
    (ι.app (op V.val) m))) hη
  change _ = coefficientRestriction I f F (leOfHom i)
    ((reesPushforwardSectionsIso I f F).hom.app (op V.val)
      ((reesPowerAffineSectionsIso I f F V).hom (ι.app (op V.val) m))) at hm
  change (reesPushforwardSectionsIso I f F).hom.app (op U.val)
      ((reesPowerAffineSectionsIso I f F U).hom
        (ι.app (op U.val) (powerRestriction I f F n (leOfHom i) m))) = _
  have hu := reesPowerAffineSectionsIso_ι I f F U n
    (powerRestriction I f F n (leOfHom i) m)
  have hv := reesPowerAffineSectionsIso_ι I f F V n m
  exact hu.trans ((homogeneousSectionMap_restriction I f F n U.property V.property
    (leOfHom i) m).symm.trans
      ((congrArg (coefficientRestriction I f F (leOfHom i)) hv.symm).trans hm.symm))

/-- Canonical natural isomorphism on the affine basis. -/
def reesPowerAffinePresheafIso :
    (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
      moduleSectionsPresheaf X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        (∐ reesPowerFamily I f F) ≅
    (inducedFunctor (fun U : X.affineOpens => U.val)).op ⋙
      moduleSectionsPresheaf X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        (reesPushforwardCoefficient I f F) :=
  NatIso.ofComponents (fun U => reesPowerAffineSectionsIso I f F U.unop)
    (fun i => reesPowerAffineSectionsIso_naturality I f F
      ((inducedFunctor (fun U : X.affineOpens => U.val)).map i.unop))

/-- The actual geometric Rees image realizes the coproduct of the original
ideal-power coefficients as scalar-linear section sheaves. -/
def reesPowerSectionsIso :
    moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (∐ reesPowerFamily I f F) ≅
    moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPushforwardCoefficient I f F) :=
  moduleSectionsIsoOfAffine X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    _ _ (reesPowerAffinePresheafIso I f F)

end AlgebraicGeometry.Scheme.Cohomology
