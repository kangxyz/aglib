/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteProductEmbedding

/-!
# The original Chow modification with a standard projective embedding

The existing finite-product Chow morphism is followed by the constructed Segre
embedding and the existing finite-map embedding. The original modification,
dense open, and isomorphism over that open are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Chow

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- Chow's original proper modification has a standard projective embedding,
with the original structure map and original dense isomorphism open. -/
theorem exists_projective_modification {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (m : ℕ)
      (j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))) (V : X.Opens),
      IsProper p ∧ Surjective p ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (m + 1))) = p ≫ f ∧
        Dense (V : Set X) ∧ IsIso (p ∣_ V) := by
  obtain ⟨n, σ, hσ, Y, p, q, V, hbase, hp, hps, hq, hV, hViso, _⟩ :=
    exists_finite_projective_product_modification R f
  let := hσ
  have : IsFinite q := hq
  obtain ⟨m, j, hj, hjbase⟩ :=
    ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_finite_projectiveProduct
      (fun i => Option (σ i)) (fun _ => inferInstance) (fun _ => inferInstance) q
  exact ⟨Y, p, m, j, V, hp, hps, hj, hjbase.trans hbase.symm, hV, hViso⟩

end AlgebraicGeometry.Scheme.Chow
