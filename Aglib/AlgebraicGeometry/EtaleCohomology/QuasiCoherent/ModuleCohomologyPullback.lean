/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.BaseRestrictionAdditive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Adjunction.PresheafPullback

/-! # Original geometric pullback of quasicoherent additive coefficients

The coefficient arrow is the mate of literal restriction along the actual
pullback projection. It uses the original over-category counit and the original
module pullback-composition comparison. No comparison on cohomology is used to
define this arrow. In particular the inverse-image unit equation is an equation
of the original sheaf maps, before passing to cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]

/-- Pullback of actual section coefficients, before taking the inverse-image mate.
The first factor restricts along the actual pullback projection; the second is
precisely the original module pullback-composition isomorphism. -/
def additiveCoefficientPullbackUnit :
    additiveCoefficient Y M ⟶
      (directImage f).obj (additiveCoefficient X ((pullback f).obj M)) where
  hom := Functor.whiskerLeft (Scheme.Etale.forget Y).op
    (Adjunction.presheafPullbackUnit (Over.mapPullbackAdj f)
      (additiveSectionsPresheaf Y M)
      (additiveSectionsPresheaf X ((pullback f).obj M))
      (additiveBaseRestrictionIso f M).hom)

/-- The actual additive inverse-image coefficient arrow, defined by the native
adjunction rather than by transport of cohomology groups. -/
def additiveCoefficientPullback :
    (inverseImage f).obj (additiveCoefficient Y M) ⟶
      additiveCoefficient X ((pullback f).obj M) :=
  ((inverseImageAdjunction f).homEquiv _ _).symm
    (additiveCoefficientPullbackUnit f M)

/-- The whole original inverse-image unit square for the coefficient arrow. -/
@[reassoc]
theorem additiveCoefficientPullback_unit :
    (inverseImageAdjunction f).unit.app (additiveCoefficient Y M) ≫
        (directImage f).map (additiveCoefficientPullback f M) =
      additiveCoefficientPullbackUnit f M := by
  exact ((inverseImageAdjunction f).homEquiv_unit
    (f := additiveCoefficientPullback f M)).symm.trans
      (((inverseImageAdjunction f).homEquiv _ _).apply_symm_apply
        (additiveCoefficientPullbackUnit f M))

/-- Geometric pullback on the original étale cohomology of a native module.
The source and target Ext universes are independent; only coefficient values
have the original fixed size `u + 1`. -/
def additiveCoefficientCohomologyPullback
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} X)] (q : ℕ) :
    Sheaf.H.{e} (additiveCoefficient Y M) q →+
      Sheaf.H.{e'} (additiveCoefficient X ((pullback f).obj M)) q :=
  (Sheaf.H.map (additiveCoefficientPullback f M) q).comp
    (cohomologyPullback f (additiveCoefficient Y M) q)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
