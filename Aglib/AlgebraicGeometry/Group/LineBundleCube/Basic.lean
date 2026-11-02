/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The cube expression on original line-bundle classes

The seven-term expression is defined using the original morphisms to a group
scheme and native Picard pullback. Its pullback law and three unit laws use
only the group operations and `Pic(Spec k) = 0`; they need no properness,
smoothness or representability hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {G T T' : Over (Spec (.of k))} [GrpObj G]

omit [GrpObj G] in
/-- A class pulled back by any constant field-valued morphism vanishes on
every test scheme, including nonreduced ones. -/
theorem pullbackClass_constant (x : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (a : PicardGroup G.left) :
    pullbackClass (toUnit T ≫ x).left a = 0 := by
  have hzero : pullbackClass x.left a = 0 := by
    change (pullbackClass x.left a : PicardGroup (Spec (.of k))) = 0
    exact Subsingleton.elim _ _
  rw [Over.comp_left, pullbackClass_comp, hzero]
  exact map_zero (pullbackHom _)

/-- Pullback by the original constant identity morphism has zero Picard class,
over every test scheme. -/
theorem pullbackClass_one (a : PicardGroup G.left) :
    pullbackClass (1 : T ⟶ G).left a = 0 := by
  exact pullbackClass_constant η[G] a

/-- The original seven-term cube expression for three scheme morphisms. -/
def cubeClass (f g h : T ⟶ G) (a : PicardGroup G.left) : PicardGroup T.left :=
  pullbackHom (f * g * h).left a - pullbackHom (f * g).left a -
    pullbackHom (f * h).left a - pullbackHom (g * h).left a +
    pullbackHom f.left a + pullbackHom g.left a + pullbackHom h.left a

/-- The whole cube expression commutes with the original test-scheme
pullback, before any geometric specialization. -/
theorem cubeClass_pullback (q : T' ⟶ T) (f g h : T ⟶ G) (a : PicardGroup G.left) :
    pullbackHom q.left (cubeClass f g h a) =
      cubeClass (q ≫ f) (q ≫ g) (q ≫ h) a := by
  simp only [cubeClass, map_add, map_sub, pullbackHom_apply,
    ← pullbackClass_comp, ← Over.comp_left, MonObj.comp_mul]

@[simp]
theorem cubeClass_one_left (g h : T ⟶ G) (a : PicardGroup G.left) :
    cubeClass 1 g h a = 0 := by
  simp only [cubeClass, _root_.one_mul, pullbackHom_apply, pullbackClass_one]
  abel

@[simp]
theorem cubeClass_one_middle (f h : T ⟶ G) (a : PicardGroup G.left) :
    cubeClass f 1 h a = 0 := by
  simp only [cubeClass, _root_.one_mul, _root_.mul_one, pullbackHom_apply, pullbackClass_one]
  abel

@[simp]
theorem cubeClass_one_right (f g : T ⟶ G) (a : PicardGroup G.left) :
    cubeClass f g 1 a = 0 := by
  simp only [cubeClass, _root_.mul_one, pullbackHom_apply, pullbackClass_one]
  abel

end AlgebraicGeometry.Scheme.Group.LineBundleCube
