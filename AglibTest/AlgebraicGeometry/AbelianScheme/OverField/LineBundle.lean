/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Square
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Symmetric
/-! The original cube and multiplication interfaces. The arbitrary test
scheme in the first example has no reducedness or Noetherian hypothesis. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Scheme.Modules.Invertible Scheme.Group.LineBundleCube

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

example {T : Over (Spec (.of k))} (f g h : T ⟶ G) (a : PicardGroup G.left) :
    cubeClass f g h a = 0 := cubeClass_eq_zero G f g h a

example (a : PicardGroup G.left) (n : ℕ) :
    pullbackClass ((𝟙 G) ^ n).left a =
      (n * (n + 1) / 2) • a + (n * (n - 1) / 2) • pullbackClass ((𝟙 G)⁻¹).left a :=
  pullbackClass_multiplication G a n

example (L : LineBundle G.left)
    (hL : pullbackClass ((𝟙 G)⁻¹).left (classOf _ L) = classOf _ L) (n : ℕ) :
    Nonempty ((pullbackLineBundle ((𝟙 G) ^ n).left L).val ≅
      (tensorPowerLineBundle G.left L (n ^ 2)).val) :=
  nonempty_multiplicationPullbackIso_of_symmetric G L hL n

/--
info: 'AlgebraicGeometry.Scheme.Group.LineBundleCube.cubeClass_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubeClass_eq_zero

/--
info: 'AlgebraicGeometry.Scheme.Group.LineBundleCube.pullbackClass_translation_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullbackClass_translation_mul

/--
info: 'AlgebraicGeometry.Scheme.Group.LineBundleCube.nonempty_multiplicationPullbackIso_of_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_multiplicationPullbackIso_of_symmetric
