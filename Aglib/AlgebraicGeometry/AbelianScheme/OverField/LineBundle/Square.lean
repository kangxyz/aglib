/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Cube
/-!
# The square identity on the original translations

The translations are Mathlib's `GrpObj.mulRight`, and every class is the
native Picard class. The theorem is the cube identity with two constant maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

/-- The theorem of the square for the actual right translations. -/
theorem pullbackClass_translation_mul
    (x y : 𝟙_ (Over (Spec (.of k))) ⟶ G) (a : PicardGroup G.left) :
    pullbackClass (GrpObj.mulRight (x * y)).hom.left a + a =
      pullbackClass (GrpObj.mulRight x).hom.left a +
        pullbackClass (GrpObj.mulRight y).hom.left a := by
  have hc := cubeClass_eq_zero G (𝟙 G) (toUnit G ≫ x) (toUnit G ≫ y) a
  have hm : (𝟙 G * (toUnit G ≫ x)) * (toUnit G ≫ y) =
      (𝟙 G) * (toUnit G ≫ (x * y)) := by rw [MonObj.comp_mul, _root_.mul_assoc]
  have hxy : (toUnit G ≫ x) * (toUnit G ≫ y) = toUnit G ≫ (x * y) :=
    (MonObj.comp_mul _ _ _).symm
  simp only [cubeClass, hm, hxy, pullbackHom_apply, pullbackClass_constant,
    Over.id_left, pullbackClass_id, sub_zero, add_zero] at hc
  apply sub_eq_zero.mp
  change pullbackClass ((𝟙 G) * (toUnit G ≫ (x * y))).left a + a -
    (pullbackClass ((𝟙 G) * (toUnit G ≫ x)).left a +
      pullbackClass ((𝟙 G) * (toUnit G ≫ y)).left a) = 0
  convert hc using 1
  abel

end AlgebraicGeometry.Scheme.Group.LineBundleCube
