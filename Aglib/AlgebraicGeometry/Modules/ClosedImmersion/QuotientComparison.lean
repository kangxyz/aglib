/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Descent
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Unit

/-! # Unit-preserving comparison of closed-immersion quotients -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
  [IsClosedImmersion i] [IsClosedImmersion j]

/-- Descend the original unit when the first kernel ideal is contained in the second. -/
def closedImmersionQuotientMap (h : i.ker ≤ j.ker) (M : X.Modules) :
    (pushforward i).obj ((pullback i).obj M) ⟶
      (pushforward j).obj ((pullback j).obj M) :=
  (pushforward i).map ((pullback i).map ((pullbackPushforwardAdjunction j).unit.app M)) ≫
    (closedImmersionDescentIso i _ (killedByIdealSheaf_of_le h
      (killedByIdealSheaf_pushforward_ker j ((pullback j).obj M)))).hom

omit [IsClosedImmersion j] in
@[reassoc (attr := simp)]
theorem closedImmersionUnit_quotientMap (h : i.ker ≤ j.ker) (M : X.Modules) :
    (pullbackPushforwardAdjunction i).unit.app M ≫
      closedImmersionQuotientMap i j h M =
        (pullbackPushforwardAdjunction j).unit.app M := by
  dsimp only [closedImmersionQuotientMap]
  have hn : (pullbackPushforwardAdjunction i).unit.app M ≫
      (pushforward i).map ((pullback i).map ((pullbackPushforwardAdjunction j).unit.app M)) =
      (pullbackPushforwardAdjunction j).unit.app M ≫
        (pullbackPushforwardAdjunction i).unit.app
          ((pushforward j).obj ((pullback j).obj M)) :=
    ((pullbackPushforwardAdjunction i).unit.naturality _).symm
  rw [← Category.assoc, hn, Category.assoc]
  let e := closedImmersionDescentIso i _ (killedByIdealSheaf_of_le h
    (killedByIdealSheaf_pushforward_ker j ((pullback j).obj M)))
  change (pullbackPushforwardAdjunction j).unit.app M ≫ e.inv ≫ e.hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Closed immersions with equal native kernel ideals induce the same quotient,
canonically on the original adjunction units. -/
def closedImmersionQuotientIso (h : i.ker = j.ker) (M : X.Modules) :
    (pushforward i).obj ((pullback i).obj M) ≅
      (pushforward j).obj ((pullback j).obj M) where
  hom := closedImmersionQuotientMap i j h.le M
  inv := closedImmersionQuotientMap j i h.ge M
  hom_inv_id := by
    apply (cancel_epi ((pullbackPushforwardAdjunction i).unit.app M)).mp
    simp
  inv_hom_id := by
    apply (cancel_epi ((pullbackPushforwardAdjunction j).unit.app M)).mp
    simp

@[reassoc (attr := simp)]
theorem closedImmersionUnit_quotientIso_hom (h : i.ker = j.ker) (M : X.Modules) :
    (pullbackPushforwardAdjunction i).unit.app M ≫
      (closedImmersionQuotientIso i j h M).hom =
        (pullbackPushforwardAdjunction j).unit.app M :=
  closedImmersionUnit_quotientMap i j h.le M

/-- Comparison commutes with every original coefficient morphism. -/
@[reassoc]
theorem closedImmersionQuotientIso_naturality (h : i.ker = j.ker)
    {M N : X.Modules} (g : M ⟶ N) :
    (pushforward i).map ((pullback i).map g) ≫
      (closedImmersionQuotientIso i j h N).hom =
    (closedImmersionQuotientIso i j h M).hom ≫
      (pushforward j).map ((pullback j).map g) := by
  apply (cancel_epi ((pullbackPushforwardAdjunction i).unit.app M)).mp
  have hi : (pullbackPushforwardAdjunction i).unit.app M ≫
      (pushforward i).map ((pullback i).map g) =
      g ≫ (pullbackPushforwardAdjunction i).unit.app N :=
    ((pullbackPushforwardAdjunction i).unit.naturality g).symm
  have hj : (pullbackPushforwardAdjunction j).unit.app M ≫
      (pushforward j).map ((pullback j).map g) =
      g ≫ (pullbackPushforwardAdjunction j).unit.app N :=
    ((pullbackPushforwardAdjunction j).unit.naturality g).symm
  rw [← Category.assoc, hi, Category.assoc, closedImmersionUnit_quotientIso_hom,
    ← Category.assoc, closedImmersionUnit_quotientIso_hom, hj]

end AlgebraicGeometry.Scheme.Modules
