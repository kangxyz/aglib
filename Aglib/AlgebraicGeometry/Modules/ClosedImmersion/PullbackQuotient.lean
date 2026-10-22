/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Square
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-! # Pullback of the original closed-immersion quotient

The comparison uses affine base change for the closed immersion, not flatness
of the arbitrary changing morphism. It preserves the original quotient unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (p : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]

/-- Pullback commutes with the actual closed-immersion quotient. -/
def closedImmersionPullbackQuotientIso :
    (pullback p).obj ((pushforward i).obj ((pullback i).obj M)) ≅
      (pushforward (Limits.pullback.snd i p)).obj
        ((pullback (Limits.pullback.snd i p)).obj ((pullback p).obj M)) := by
  let a := Limits.pullback.fst i p
  let q := Limits.pullback.snd i p
  let e := BaseChange.Affine.Square.pullbackSquareIso a q i p Limits.pullback.condition
  letI := moduleBaseChangeMap_isIso i p ((pullback i).obj M)
  exact asIso (moduleBaseChangeMap i p ((pullback i).obj M)) ≪≫
    (pushforward q).mapIso (e.app M).symm

@[reassoc (attr := simp)]
theorem closedImmersionPullbackQuotientIso_unit :
    (pullback p).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
      (closedImmersionPullbackQuotientIso i p M).hom =
        (pullbackPushforwardAdjunction (Limits.pullback.snd i p)).unit.app
          ((pullback p).obj M) := by
  let a := Limits.pullback.fst i p
  let q := Limits.pullback.snd i p
  let e := BaseChange.Affine.Square.pullbackSquareIso a q i p Limits.pullback.condition
  have hu := unit_mateEquiv (pullbackPushforwardAdjunction i)
    (pullbackPushforwardAdjunction q) e.hom M
  change (pullback p).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
      (BaseChange.Affine.Square.baseChangeNatTransOfSquare a q i p
        Limits.pullback.condition).app ((pullback i).obj M) = _ at hu
  rw [BaseChange.Affine.Square.baseChangeNatTransOfSquare_app,
    BaseChange.Affine.Square.moduleSquareBaseChangeMap_eq] at hu
  change (pullback p).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
    moduleBaseChangeMap i p ((pullback i).obj M) ≫
      (pushforward q).map (e.inv.app M) = _
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp]
  simp
  rfl

end AlgebraicGeometry.Scheme.Modules
