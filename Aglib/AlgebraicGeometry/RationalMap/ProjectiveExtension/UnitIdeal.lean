/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.Basic

/-!
# The actual ideal frame on its unit locus

On an open where a given ideal becomes the unit ideal, the actual pulled
ideal module is canonically the structure module. Its forward map is the
pulled inclusion followed by the original pullback-unit comparison. This is
an equality of maps, not merely existence of a line-module trivialization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

/-- The actual unit-ideal inclusion is an isomorphism: its defining structure
map has empty source and hence is zero. -/
theorem idealInclusion_top_isIso (X : Scheme.{u}) :
    IsIso (Hom.idealInclusion (⊤ : X.IdealSheafData).subschemeι) := by
  change IsIso (kernel.ι (Hom.structureModuleMap (⊤ : X.IdealSheafData).subschemeι))
  rw [Blowup.structureModuleMap_eq_zero_of_isEmpty]
  infer_instance

variable {X Y : Scheme.{u}} (K : X.IdealSheafData) (j : Y ⟶ X) [IsOpenImmersion j]
variable (hK : K.comap j = ⊤)

/-- The canonical pulled-ideal frame on the specified unit locus. -/
def unitLocusIdealIso :
    (Scheme.Modules.pullback j).obj (Hom.idealModule K.subschemeι) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  let : IsIso (baseIdealPullbackMap K j) :=
    Hom.idealPullbackMap_isIso_of_isOpenImmersion K.subschemeι (K.comap j).subschemeι j
      (baseIdealSourceMap K j) (baseIdealSourceMap_comm K j)
      (baseIdealSourceMap_isPullback K j)
  let : IsIso (Hom.idealInclusion (K.comap j).subschemeι) := by
    rw [hK]
    exact idealInclusion_top_isIso Y
  exact asIso (baseIdealPullbackMap K j) ≪≫
    asIso (Hom.idealInclusion (K.comap j).subschemeι)

/-- The forward map is the actual pulled inclusion, with its original unit
comparison; no independently chosen frame or scalar occurs. -/
@[reassoc]
theorem unitLocusIdealIso_hom :
    (unitLocusIdealIso K j hK).hom =
      (Scheme.Modules.pullback j).map (Hom.idealInclusion K.subschemeι) ≫
        (pullbackUnitIso j).hom :=
  baseIdealPullbackMap_inclusion K j

end AlgebraicGeometry.Scheme.RationalCoordinates
