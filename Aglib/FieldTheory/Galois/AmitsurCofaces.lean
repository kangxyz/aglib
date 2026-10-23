/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.AmitsurCoordinates

/-! # The original Amitsur cofaces in Galois coordinates

These equalities concern the native conerve maps themselves. The cumulative
coordinates give exactly the inhomogeneous multiplicative group-cochain faces.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Simplicial

namespace Algebra.Amitsur

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Evaluate the original first Amitsur term at a Galois coordinate. -/
def oneEvaluation (σ : Gal(L/K)) : term K L 1 ⟶ CommAlgCat.of K L :=
  CommAlgCat.ofHom ((Pi.evalAlgHom K (fun _ : Gal(L/K) => L) σ).comp
    (oneGaloisEquiv K L).toAlgHom)

/-- Evaluate the original second Amitsur term at cumulative coordinates. -/
def twoEvaluation (σ τ : Gal(L/K)) : term K L 2 ⟶ CommAlgCat.of K L :=
  CommAlgCat.ofHom ((Pi.evalAlgHom K (fun _ : Gal(L/K) => L) σ).comp
    ((Pi.evalAlgHom K (fun _ : Gal(L/K) => Gal(L/K) → L) τ).comp
      (twoGaloisEquiv K L).toAlgHom))

/-- Evaluate the original third Amitsur term at cumulative coordinates. -/
def threeEvaluation (σ τ υ : Gal(L/K)) : term K L 3 ⟶ CommAlgCat.of K L :=
  CommAlgCat.ofHom ((Pi.evalAlgHom K (fun _ : Gal(L/K) => L) σ).comp
    ((Pi.evalAlgHom K (fun _ : Gal(L/K) => Gal(L/K) → L) τ).comp
      ((Pi.evalAlgHom K (fun _ : Gal(L/K) => Gal(L/K) → Gal(L/K) → L) υ).comp
        (threeGaloisEquiv K L).toAlgHom)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 0 in original degree 1 has the literal group-cochain formula. -/
theorem δ_0_twoEvaluation (σ τ : Gal(L/K)) :
    (conerve K L).δ 0 ≫ twoEvaluation K L σ τ =
      oneEvaluation K L τ ≫ CommAlgCat.ofHom σ.toAlgHom := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change twoGaloisEquiv K L ((ι K L 2 ((0 : Fin 3).succAbove i)).hom x)
    τ σ = σ (oneGaloisEquiv K L ((ι K L 1 i).hom x) τ)
  rw [twoGaloisEquiv_ι, oneGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 1 in original degree 1 has the literal group-cochain formula. -/
theorem δ_1_twoEvaluation (σ τ : Gal(L/K)) :
    (conerve K L).δ 1 ≫ twoEvaluation K L σ τ =
      oneEvaluation K L (σ * τ) := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change twoGaloisEquiv K L ((ι K L 2 ((1 : Fin 3).succAbove i)).hom x)
    τ σ = oneGaloisEquiv K L ((ι K L 1 i).hom x) (σ * τ)
  rw [twoGaloisEquiv_ι, oneGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 2 in original degree 1 has the literal group-cochain formula. -/
theorem δ_2_twoEvaluation (σ τ : Gal(L/K)) :
    (conerve K L).δ 2 ≫ twoEvaluation K L σ τ =
      oneEvaluation K L σ := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change twoGaloisEquiv K L ((ι K L 2 ((2 : Fin 3).succAbove i)).hom x)
    τ σ = oneGaloisEquiv K L ((ι K L 1 i).hom x) σ
  rw [twoGaloisEquiv_ι, oneGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 0 in original degree 2 has the literal group-cochain formula. -/
theorem δ_0_threeEvaluation (σ τ υ : Gal(L/K)) :
    (conerve K L).δ 0 ≫ threeEvaluation K L σ τ υ =
      twoEvaluation K L τ υ ≫ CommAlgCat.ofHom σ.toAlgHom := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change threeGaloisEquiv K L ((ι K L 3 ((0 : Fin 4).succAbove i)).hom x)
    υ τ σ = σ (twoGaloisEquiv K L ((ι K L 2 i).hom x) υ τ)
  rw [threeGaloisEquiv_ι, twoGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 1 in original degree 2 has the literal group-cochain formula. -/
theorem δ_1_threeEvaluation (σ τ υ : Gal(L/K)) :
    (conerve K L).δ 1 ≫ threeEvaluation K L σ τ υ =
      twoEvaluation K L (σ * τ) υ := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change threeGaloisEquiv K L ((ι K L 3 ((1 : Fin 4).succAbove i)).hom x)
    υ τ σ = twoGaloisEquiv K L ((ι K L 2 i).hom x) υ (σ * τ)
  rw [threeGaloisEquiv_ι, twoGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 2 in original degree 2 has the literal group-cochain formula. -/
theorem δ_2_threeEvaluation (σ τ υ : Gal(L/K)) :
    (conerve K L).δ 2 ≫ threeEvaluation K L σ τ υ =
      twoEvaluation K L σ (τ * υ) := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change threeGaloisEquiv K L ((ι K L 3 ((2 : Fin 4).succAbove i)).hom x)
    υ τ σ = twoGaloisEquiv K L ((ι K L 2 i).hom x) (τ * υ) σ
  rw [threeGaloisEquiv_ι, twoGaloisEquiv_ι]
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coface 3 in original degree 2 has the literal group-cochain formula. -/
theorem δ_3_threeEvaluation (σ τ υ : Gal(L/K)) :
    (conerve K L).δ 3 ≫ threeEvaluation K L σ τ υ =
      twoEvaluation K L σ τ := by
  apply term_hom_ext
  intro i
  rw [ι_δ_assoc]
  apply CommAlgCat.hom_ext
  ext x
  change threeGaloisEquiv K L ((ι K L 3 ((3 : Fin 4).succAbove i)).hom x)
    υ τ σ = twoGaloisEquiv K L ((ι K L 2 i).hom x) τ σ
  rw [threeGaloisEquiv_ι, twoGaloisEquiv_ι]
  fin_cases i <;> rfl

end Algebra.Amitsur
