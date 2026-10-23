/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.PointImage
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Fibers

/-!
# Surjectivity of the original binary-form coefficient morphism

The original coefficient factorization lifts every actual algebraically
closed field-valued target point through the same original product morphism.
The native geometric-point criterion then gives actual surjectivity over
every original commutative base ring, including the empty product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The original multiplication morphism is surjective over every commutative base ring. -/
instance multiplication_surjective : Surjective (multiplication R n) := by
  apply surjective_of_geometric_point_lifting
  intro K _ _ g
  let β : R →+* K := (Spec.preimage (g ≫ toSpec R (ULift.{u} (Fin (n + 1))))).hom
  have hβ : Spec.map (CommRingCat.ofHom β) =
      g ≫ toSpec R (ULift.{u} (Fin (n + 1))) := Spec.map_preimage _
  obtain ⟨v, k₀, hk, hv⟩ := Field.exists_point β g hβ.symm
  obtain ⟨a, c, hc, ha⟩ := Field.exists_coefficient_factorization
    (fun j : Fin (n + 1) => v (ULift.up j)) ⟨k₀.down, by simpa only [ULift.up_down] using hk⟩
  obtain ⟨j₀, hj⟩ := Field.exists_nonzero_coefficient a
  refine ⟨Field.sourcePoint β a, (Field.multiplication_on_sourcePoint β a j₀ hj).trans ?_⟩
  apply Eq.trans _ hv
  exact Field.point_eq_of_scale β (Field.productVector a) v (ULift.up j₀) k₀ hj hk c hc
    (fun j => by simpa only [Field.productVector, ULift.up_down] using ha j.down)

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
