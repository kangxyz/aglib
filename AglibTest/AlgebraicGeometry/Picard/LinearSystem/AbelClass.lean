/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.AbelClass

/-!
# Consumer checks for Abel classes of linear-system divisors

A relative effective Cartier divisor lies in `LinSys_{L/X/S}(T)` exactly when its Abel class differs
from `g_T^*[L]` by a class pulled back from `T` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 3.12, p. 25); divisors of `X_V ×_V U ⟶ U` transport to `X ×_S U` along
`X ×_S U ≅ X_V ×_V U`, with their Abel classes; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.RelativePicard Scheme.LinearSystem

universe u

namespace AglibTest.LinearSystemAbelClass

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Two classes have the same image in `P_{X/S}(T)` exactly when they differ by a base class. -/
example {T : Over S} (x y : PicardGroup (pullback p T.hom)) :
    ((quotientProjection p).app (op T)).hom x = ((quotientProjection p).app (op T)).hom y ↔
      ∃ n : PicardGroup T.left, x = y + pullbackClass (pullback.snd p T.hom) n :=
  quotientProjection_app_eq_iff p x y

/-- The linear-system condition in Abel-class form, in both shapes, and its fppf image. -/
example (L : LineBundle X) {T : Over S} {D : (pullback p T.hom).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    (IsLinearSystemDivisor p L T D ↔ ∃ n : PicardGroup T.left,
      abelClass p D hD = pullbackClass (pullback.fst p T.hom) (classOf X L) +
        pullbackClass (pullback.snd p T.hom) n) ∧
    (IsLinearSystemDivisor p L T D ↔
      abelClass p D hD - pullbackClass (pullback.fst p T.hom) (classOf X L) ∈ baseImage p (op T)) ∧
    (∀ h : IsLinearSystemDivisor p L T D, fppfAbelClass p D h.1 =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op T)
        (pullbackClass (pullback.fst p T.hom) (classOf X L))) :=
  ⟨isLinearSystemDivisor_iff_exists_abelClass_eq p L hD,
    isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage p L hD,
    fun h => fppfAbelClass_eq_of_isLinearSystemDivisor p L h⟩

/-- Transport along `X ×_S U ≅ X_V ×_V U`: relative effective Cartier divisors in both
directions, the round trips, and the Abel class. -/
example {U V : Over S} (g : U ⟶ V)
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left))
    {D' : (pullback p U.hom).IdealSheafData}
    (hD' : Scheme.Hom.IsRelativeEffectiveCartier D'.subschemeι (pullback.snd p U.hom)) :
    Scheme.Hom.IsRelativeEffectiveCartier
        (D'.comap (isPullback_familyMap p g).isoPullback.inv).subschemeι
        (pullback.snd (pullback.snd p V.hom) g.left) ∧
      (D'.comap (isPullback_familyMap p g).isoPullback.inv).comap
        (isPullback_familyMap p g).isoPullback.hom = D' ∧
      (D.comap (isPullback_familyMap p g).isoPullback.hom).comap
        (isPullback_familyMap p g).isoPullback.inv = D ∧
      abelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
          (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD) =
        pullbackClass (isPullback_familyMap p g).isoPullback.hom
          (abelClass (pullback.snd p V.hom) (T := Over.mk g.left) D hD) :=
  ⟨isRelativeEffectiveCartier_comap_isoPullback_inv p g hD',
    comap_isoPullback_inv_comap_hom p g D', comap_isoPullback_hom_comap_inv p g D,
    abelClass_comap_isoPullback_hom p g hD⟩

/-- Linear-system divisors over `V`, transported to `X ×_S U`, and their fppf Abel classes. -/
example {U V : Over S} (g : U ⟶ V) (L : LineBundle (pullback p V.hom))
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left)) :
    (IsLinearSystemDivisor (pullback.snd p V.hom) L (Over.mk g.left) D ↔
      abelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
          (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD) -
        pullbackClass (familyMap p g) (classOf _ L) ∈ baseImage p (op U)) ∧
    (∀ h : IsLinearSystemDivisor (pullback.snd p V.hom) L (Over.mk g.left) D,
      fppfAbelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
          (isRelativeEffectiveCartier_comap_isoPullback_hom p g h.1) =
        (fppfPicardSheaf p).obj.map g.op
          ((quotientProjection p ≫ toFppfPicardSheaf p).app (op V) (classOf _ L))) :=
  ⟨isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage p g L hD,
    fun h => fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor p g L h⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.quotientProjection_app_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quotientProjection_app_eq_iff

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isLinearSystemDivisor_iff_exists_abelClass_eq' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLinearSystemDivisor_iff_exists_abelClass_eq

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.fppfAbelClass_eq_of_isLinearSystemDivisor' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfAbelClass_eq_of_isLinearSystemDivisor

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isRelativeEffectiveCartier_comap_isoPullback_hom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isRelativeEffectiveCartier_comap_isoPullback_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isRelativeEffectiveCartier_comap_isoPullback_inv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isRelativeEffectiveCartier_comap_isoPullback_inv

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.abelClass_comap_isoPullback_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelClass_comap_isoPullback_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_isoPullback_hom_mem_baseImage_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullbackClass_isoPullback_hom_mem_baseImage_iff

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor

end AglibTest.LinearSystemAbelClass
