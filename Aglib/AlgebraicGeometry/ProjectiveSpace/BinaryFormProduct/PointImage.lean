/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.PointEvaluation

/-!
# The actual coefficient morphism on normalized product points

The image of the original product point is the actual relative projective
point of its original product coefficient vector. This comparison is an
equality of the same scheme morphisms over the same original coefficient map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

variable {R K : Type u} [CommRing R] [Field K] {n : ℕ}

/-- The original descending-degree vector of the normalized factor family. -/
def productVector (a : Fin n → Option K) (j : ULift.{u} (Fin (n + 1))) : K :=
  coefficient (fun i => first (a i)) (fun i => second (a i)) j.down

/-- Multiplication sends the actual original normalized product point to
the actual projective point of its original coefficient vector. -/
theorem multiplication_on_sourcePoint (β : R →+* K) (a : Fin n → Option K)
    (j₀ : Fin (n + 1))
    (hj : coefficient (fun i => first (a i)) (fun i => second (a i)) j₀ ≠ 0) :
    sourcePoint β a ≫ multiplication R n =
      point β (productVector a) (ULift.up j₀) hj := by
  let g := sourcePoint β a ≫ multiplication R n
  have hg : g ≫ toSpec R (ULift.{u} (Fin (n + 1))) =
      Spec.map (CommRingCat.ofHom β) := by
    dsimp only [g]
    rw [Category.assoc, multiplication_over, sourcePoint_over]
  obtain ⟨v, k₀, hk, hv⟩ := exists_point β g hg
  have hvj : v (ULift.up j₀) ≠ 0 := by
    intro hz
    have hm : (default : Spec (.of K)) ∈
        point β v k₀ hk ⁻¹ᵁ coordinateOpen R (ULift.{u} (Fin (n + 1))) (ULift.up j₀) := by
      simpa only [hv] using sourcePoint_multiplication_preimage β a j₀ hj
        (show (default : Spec (.of K)) ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
    rw [point_preimage_zero β v k₀ hk (ULift.up j₀) hz] at hm
    exact hm
  have he : point β v (ULift.up j₀) hvj = g :=
    (point_eq_of_scale β v v (ULift.up j₀) k₀ hvj hk 1 one_ne_zero
      (fun _ => (one_mul _).symm)).trans hv
  have hvector (j : ULift.{u} (Fin (n + 1))) :
      productVector a j = (productVector a (ULift.up j₀) / v (ULift.up j₀)) * v j := by
    have hr := sourcePoint_multiplication_coefficient_mul_ratio β a j₀ hj j
    have hp := point_ratio β v (ULift.up j₀) hvj j
    simp only [he] at hp
    rw [hp, ← map_mul] at hr
    have hK := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.injective hr
    change productVector a (ULift.up j₀) * (v j * (v (ULift.up j₀))⁻¹) =
      productVector a j at hK
    rw [← hK, div_eq_mul_inv]
    ring
  exact hv.symm.trans (point_eq_of_scale β v (productVector a) k₀ (ULift.up j₀) hk hj
    (productVector a (ULift.up j₀) / v (ULift.up j₀)) (div_ne_zero hj hvj) hvector)

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field
