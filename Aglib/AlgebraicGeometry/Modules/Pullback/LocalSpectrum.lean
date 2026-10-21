/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.SectionStalk
public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit
public import Aglib.AlgebraicGeometry.Modules.Stalk.LocalSpectrum

/-!
# Pullback to the spectrum of the local ring

Global sections of the actual pullback along `fromSpecStalk` recover the
original module stalk. The comparison retains the native extension-of-scalars
unit, the actual pullback-stalk isomorphism, and the inverse closed-point germ.
No quasicoherence or finite-type hypothesis is needed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (Y : Scheme.{u}) (y : Y)

/-- The actual stalk map of `fromSpecStalk`, after transporting its source point,
is the inverse of the native closed-point identification. -/
theorem fromSpecStalk_normalized_stalkMap :
    (Y.presheaf.stalkCongr (.of_eq (Scheme.fromSpecStalk_closedPoint (x := y)))).inv ≫
        (Y.fromSpecStalk y).stalkMap (closedPoint (Y.presheaf.stalk y)) =
      (stalkClosedPointIso (Y.presheaf.stalk y)).inv := by
  apply (cancel_mono (stalkClosedPointIso (Y.presheaf.stalk y)).hom).1
  rw [Category.assoc, ← Scheme.stalkClosedPointTo,
    Scheme.stalkClosedPointTo_fromSpecStalk, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The canonical pullback-stalk comparison with both local rings normalized
by the actual point and closed-point ring identifications. -/
def fromSpecStalkPullbackStalkIso :
    pullback (Y.fromSpecStalk y) ⋙
        moduleStalk (Spec (Y.presheaf.stalk y)) (closedPoint (Y.presheaf.stalk y)) ≅
      moduleStalk Y y ⋙
        ModuleCat.extendScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom := by
  simpa only [fromSpecStalk_normalized_stalkMap] using
    pullbackModuleStalkAtEqIso (Y.fromSpecStalk y) (closedPoint (Y.presheaf.stalk y)) y
      (Scheme.fromSpecStalk_closedPoint (x := y))

/-- Extension followed by restriction along the native closed-point ring
isomorphism has the original scalar-extension unit as its equivalence. -/
def closedPointScalarExtensionUnitIso (R : CommRingCat.{u}) [IsLocalRing R]
    (M : ModuleCat.{u} R) :
    M ≅ (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).obj
      ((ModuleCat.extendScalars (stalkClosedPointIso R).inv.hom).obj M) := by
  letI : (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      ((stalkClosedPointIso R).symm.commRingCatIsoToRingEquiv)
  exact asIso ((ModuleCat.extendRestrictScalarsAdj (stalkClosedPointIso R).inv.hom).unit.app M)

/-- The original local-ring module stalk identifies with global sections of
its actual geometric pullback to the local spectrum. -/
def stalkFromSpecStalkSectionsIso (M : Y.Modules) :
    (moduleStalk Y y).obj M ≅
      moduleSpecΓFunctor.obj ((pullback (Y.fromSpecStalk y)).obj M) :=
  closedPointScalarExtensionUnitIso (Y.presheaf.stalk y) ((moduleStalk Y y).obj M) ≪≫
    (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).mapIso
      ((fromSpecStalkPullbackStalkIso Y y).app M).symm ≪≫
    (localSpectrumSectionsStalkIso (Y.presheaf.stalk y)
      ((pullback (Y.fromSpecStalk y)).obj M)).symm

/-- The forward comparison is exactly the original scalar unit followed by
inverse pullback-stalk and inverse germ maps. -/
theorem stalkFromSpecStalkSectionsIso_hom (M : Y.Modules) :
    (stalkFromSpecStalkSectionsIso Y y M).hom =
      (ModuleCat.extendRestrictScalarsAdj
        (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).unit.app
          ((moduleStalk Y y).obj M) ≫
      (ModuleCat.restrictScalars (stalkClosedPointIso (Y.presheaf.stalk y)).inv.hom).map
        ((fromSpecStalkPullbackStalkIso Y y).app M).inv ≫
      (localSpectrumSectionsStalkIso (Y.presheaf.stalk y)
        ((pullback (Y.fromSpecStalk y)).obj M)).inv := rfl

end AlgebraicGeometry.Scheme.Modules
