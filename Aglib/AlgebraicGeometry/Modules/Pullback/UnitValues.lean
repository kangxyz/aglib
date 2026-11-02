/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Native top-section values of original pullback units

The original equality transport, composition comparison and adjunction unit
naturality are evaluated using `Hom.app` while schemes and coefficients remain
variable. These are views of the existing maps and complete laws.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Equality of original scheme maps retains their native top-section unit values. -/
theorem pullbackCongr_unit_app_top {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤
        (((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) =
      ((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m := by
  exact pullbackCongr_unit_top h M m

/-- The original inverse composition comparison retains native top-section unit values. -/
theorem pullbackComp_inv_unit_app_top (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((pullbackComp f g).inv.app M).app ⊤
        (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app ⊤ m) =
      ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app ⊤
        (((pullbackPushforwardAdjunction g).unit.app M).app ⊤ m) := by
  exact pullbackComp_inv_unit_top f g M m

/-- Original coefficient maps commute with the native top-section adjunction unit. -/
theorem pullback_unit_naturality_app_top (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) (m : Γ(M, ⊤)) :
    ((pullbackPushforwardAdjunction f).unit.app N).app ⊤ (a.app ⊤ m) =
      ((pullback f).map a).app ⊤
        (((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) := by
  exact congrArg
    (fun q : M ⟶ (pushforward f).obj ((pullback f).obj N) => q.app ⊤ m)
    ((pullbackPushforwardAdjunction f).unit.naturality a)

end AlgebraicGeometry.Scheme.Modules
