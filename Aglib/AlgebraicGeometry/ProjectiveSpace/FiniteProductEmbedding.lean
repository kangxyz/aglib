/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.FiniteProduct
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

/-!
# Finite maps to original finite projective products

The target's actual Segre closed immersion is composed with the finite map.
The existing finite-map embedding theorem then constructs a closed embedding
of the unchanged source. Finiteness itself is never used as closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

variable {R : Type u} [CommRing R] {n : ℕ} {Y : Scheme.{u}}

/-- A finite original map to a finite projective product admits a standard
closed projective embedding with the same original structural morphism. -/
theorem exists_closedImmersion_of_finite_projectiveProduct (σ : Fin n → Type u)
    (hfinite : ∀ i, Finite (σ i)) (hnonempty : ∀ i, Nonempty (σ i))
    (q : Y ⟶ (Scheme.finiteProductOver (fun i => CategoryTheory.Over.mk
      (toSpec R (σ i)))).left) [IsFinite q] :
    ∃ (m : ℕ) (j : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (m + 1)))),
      IsClosedImmersion j ∧ j ≫ toSpec R (ULift.{u} (Fin (m + 1))) =
        q ≫ (Scheme.finiteProductOver (fun i => CategoryTheory.Over.mk
          (toSpec R (σ i)))).hom := by
  obtain ⟨τ, hτ, hτne, e, he, hebase⟩ :=
    Segre.exists_closedImmersion_finiteProductOver R σ hfinite hnonempty
  have : Finite τ := hτ
  have : Nonempty τ := hτne
  have : IsClosedImmersion e := he
  obtain ⟨m, j, hj, hjbase⟩ := exists_closedImmersion_of_isFinite (q ≫ e)
  refine ⟨m, j, hj, ?_⟩
  simpa only [Category.assoc, hebase] using hjbase

end AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding
