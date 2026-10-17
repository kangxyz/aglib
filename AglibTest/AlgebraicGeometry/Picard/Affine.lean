/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing

/-! Focused consumer of the affine Picard comparison and local triviality. The
equivalence sends the class of an actual line bundle to Mathlib's class of its actual
module of global sections; local rings are arbitrary commutative local rings. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible

universe u

example (R : CommRingCat.{u}) : PicardGroup (Spec R) ≃+ Additive (CommRing.Pic R) :=
  picardGroupEquivCommRingPic R

example (R : CommRingCat.{u}) (L : LineBundle (Spec R)) :
    picardGroupEquivCommRingPic R (classOf (Spec R) L) =
      Additive.ofMul (CommRing.Pic.mk R (moduleSpecΓFunctor.obj L.val)) :=
  rfl

example (R : CommRingCat.{u}) (L : LineBundle (Spec R)) :
    Module.Invertible R (moduleSpecΓFunctor.obj L.val) :=
  inferInstance

example {R S : CommRingCat.{u}} (φ : R ⟶ S) (a : PicardGroup (Spec R)) :
    picardGroupEquivCommRingPic S (pullbackClass (Spec.map φ) a) =
      Additive.ofMul (CommRing.Pic.mapRingHom φ.hom
        (Additive.toMul (picardGroupEquivCommRingPic R a))) :=
  picardGroupEquivCommRingPic_pullbackClass φ a

example (R : CommRingCat.{u}) (M : ModuleCat.{u} R) [Module.Invertible R M] :
    IsLocallyRankOne (Spec R) (tilde M) :=
  tilde_isLocallyRankOne M

example {X : Scheme.{u}} (L : LineBundle X) : L.val.IsQuasicoherent := inferInstance

example (R : CommRingCat.{u}) [IsLocalRing R] (L : LineBundle (Spec R)) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :=
  nonempty_iso_unit_of_isLocalRing R L

example (R : CommRingCat.{u}) [IsLocalRing R] : Subsingleton (PicardGroup (Spec R)) :=
  inferInstance

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.picardGroupEquivCommRingPic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms picardGroupEquivCommRingPic

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.subsingleton_picardGroup_of_isLocalRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms subsingleton_picardGroup_of_isLocalRing

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.picardGroupEquivCommRingPic_pullbackClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms picardGroupEquivCommRingPic_pullbackClass
