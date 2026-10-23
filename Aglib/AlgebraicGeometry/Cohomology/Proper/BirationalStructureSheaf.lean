/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars

/-!
# Original structure comparisons for a proper birational morphism

The existing birational-functions theorem identifies the original ring-sheaf
map with an isomorphism. Its components give the original structure-module
unit and the original pullback/pushforward adjunction unit as isomorphisms.
Over a normal affine domain the literal structural coefficient map is
bijective, and the original degree-zero section comparison identifies the
cohomology of the structure module with the base ring. No Noetherianity or
dimension hypothesis is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- The original structural coefficient map is bijective for a proper
birational morphism to a normal affine integral target. -/
theorem Hom.bijective_structuralCoefficients_of_isProper_birational
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  have hf : Function.Bijective f.appTop :=
    bijective_app_of_isAffineOpen_of_universallyClosed_birational f hR hff ⊤
      (isAffineOpen_top _)
  exact hf.comp (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective

namespace Modules

/-- A proper birational morphism onto a normal integral target identifies the
original structure module with its ordinary direct image. -/
theorem isIso_unitToPushforwardObjUnit_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsIso (C := Y.Modules)
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let : IsIso f.c := isIso_c_of_isProper_birational f hY hff
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (f.app U)
  let : IsIso (f.app U) := NatIso.isIso_app_of_isIso f.c (op U)
  exact ConcreteCategory.bijective_of_isIso _

/-- The original pullback/pushforward adjunction unit on the target structure
module is invertible for a proper birational morphism onto a normal integral
target. -/
theorem isIso_pullbackPushforwardAdjunction_unit_unit_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hY : NormalStalks Y)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)) := by
  let η := (pullbackPushforwardAdjunction f).unit.app
    (SheafOfModules.unit Y.ringCatSheaf)
  let β := (pushforward f).map (pullbackUnitIso f).hom
  have hunit : η ≫ β = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    simpa only [η, β, Adjunction.homEquiv_unit] using pullbackUnitIso_homEquiv f
  let : IsIso (η ≫ β) := by
    rw [hunit]
    exact isIso_unitToPushforwardObjUnit_of_isProper_birational f hY hff
  exact IsIso.of_isIso_comp_right η β

end Modules

namespace Cohomology

/-- Original degree-zero structure-module cohomology is the base ring,
linearly for the unchanged structural action, under a proper birational
morphism to a normal affine domain. The forward map sends a scalar to the
class of its original structural section. -/
def moduleH0LinearEquivOfProperBirational
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI := moduleCohomologyModuleOfHom X α O 0
    R ≃ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf X O) 0 := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  letI := moduleCohomologyModuleOfHom X α O 0
  letI : Module R (O.val.obj (op ⊤)) := Module.compHom _ α
  let c : R →ₗ[R] O.val.obj (op ⊤) := {
    toFun := fun r => α r
    map_add' := fun a b => α.map_add a b
    map_smul' := fun a b => by
      change α (a * b) = α a * α b
      exact α.map_mul a b }
  exact (LinearEquiv.ofBijective c
    (Hom.bijective_structuralCoefficients_of_isProper_birational R f hR hff)).trans
      (moduleH0EquivOfHom X α O).symm

/-- The degree-zero identification retains the literal structural section
of each scalar through the original native section comparison. -/
theorem moduleH0LinearEquivOfProperBirational_sections
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    (hR : NormalStalks (Spec (CommRingCat.of R)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (r : R) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    letI := moduleCohomologyModuleOfHom X α O 0
    moduleH0EquivOfHom X α O (moduleH0LinearEquivOfProperBirational R f hR hff r) =
      f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α O 0
  change moduleH0EquivOfHom X α O ((moduleH0EquivOfHom X α O).symm (α r)) = α r
  exact (moduleH0EquivOfHom X α O).apply_symm_apply _

end Cohomology

end AlgebraicGeometry.Scheme
