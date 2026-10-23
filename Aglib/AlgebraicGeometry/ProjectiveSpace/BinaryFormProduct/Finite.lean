/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.PointImage
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Fibers

/-!
# Finiteness of the original binary-form coefficient morphism

Every actual geometric point in an original fibre is represented by a
normalized ordered factor family of its original target polynomial.
Those families form a finite set. Properness and the native quasi-finite
criterion give finiteness of the same original coefficient morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

private theorem normalizedPolynomial_eq_of_productVector {K : Type u} [Field K] {n : ℕ}
    (a : Fin n → Option K) (v : Fin (n + 1) → K) (c : K)
    (h : ∀ j : ULift.{u} (Fin (n + 1)), Field.productVector a j = c * v j.down) :
    Field.normalizedPolynomial a = Polynomial.C c * ofCoefficients v := by
  change polynomial (fun i => Field.first (a i)) (fun i => Field.second (a i)) =
    Polynomial.C c * ofCoefficients v
  apply (Polynomial.ext_iff_natDegree_le (natDegree_polynomial_le _ _)
    ((Polynomial.natDegree_C_mul_le c (ofCoefficients v)).trans
      (natDegree_ofCoefficients_le v))).mpr
  intro m hm
  let j : Fin (n + 1) := ⟨n - m, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hj : n - j.val = m := Nat.sub_sub_self hm
  rw [← hj, Polynomial.coeff_C_mul, ofCoefficients_coeff]
  exact h (ULift.up j)

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The original multiplication morphism is finite over every commutative base ring. -/
instance multiplication_isFinite : IsFinite (multiplication R n) := by
  apply isFinite_of_finite_geometric_point_fibers
  intro K _ _ g
  classical
  let β : R →+* K := (Spec.preimage (g ≫ toSpec R (ULift.{u} (Fin (n + 1))))).hom
  have hβ : Spec.map (CommRingCat.ofHom β) =
      g ≫ toSpec R (ULift.{u} (Fin (n + 1))) := Spec.map_preimage _
  obtain ⟨v, k₀, hk, hv⟩ := Field.exists_point β g hβ.symm
  let p := ofCoefficients (fun j : Fin (n + 1) => v (ULift.up j))
  have hp : p ≠ 0 := ofCoefficients_ne_zero _
    ⟨k₀.down, by simpa only [ULift.up_down] using hk⟩
  let F := {s : Spec (.of K) ⟶ source R n // s ≫ multiplication R n = g}
  have hsource (s : F) : ∃ a : Fin n → Option K, Field.sourcePoint β a = s.val := by
    apply Field.exists_sourcePoint
    rw [← multiplication_over R n, ← Category.assoc, s.property]
    exact hβ.symm
  let a : F → (Fin n → Option K) := fun s => Classical.choose (hsource s)
  have ha (s : F) : Field.sourcePoint β (a s) = s.val := Classical.choose_spec (hsource s)
  have hfactor (s : F) : ∃ c : K, c ≠ 0 ∧
      Field.normalizedPolynomial (a s) = Polynomial.C c * p := by
    obtain ⟨j₀, hj⟩ := Field.exists_nonzero_coefficient (a s)
    have he : Field.point β (Field.productVector (a s)) (ULift.up j₀) hj =
        Field.point β v k₀ hk :=
      (Field.multiplication_on_sourcePoint β (a s) j₀ hj).symm.trans
        (((congrArg (fun t => t ≫ multiplication R n) (ha s)).trans s.property).trans hv.symm)
    obtain ⟨c, hc, hscale⟩ := Field.exists_scale_of_point_eq β v (Field.productVector (a s))
      k₀ (ULift.up j₀) hk hj he.symm
    exact ⟨c, hc, normalizedPolynomial_eq_of_productVector (a s)
      (fun j => v (ULift.up j)) c
      (fun j => by simpa only [ULift.up_down] using hscale j)⟩
  have : Finite {a : Fin n → Option K // ∃ c : K, c ≠ 0 ∧
      Field.normalizedPolynomial a = Polynomial.C c * p} :=
    Field.finite_normalized_factor_fiber p hp
  let encode : F → {a : Fin n → Option K // ∃ c : K, c ≠ 0 ∧
      Field.normalizedPolynomial a = Polynomial.C c * p} := fun s => ⟨a s, hfactor s⟩
  apply Finite.of_injective encode
  intro s t h
  apply Subtype.ext
  exact (ha s).symm.trans
    ((congrArg (Field.sourcePoint β) (congrArg Subtype.val h)).trans (ha t))

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
