/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring

/-!
# Homogeneous translations of three polynomial coordinates


Source: `R5Lab.Aglib.RingTheory.MvPolynomial.HomogeneousTranslation`.
Packet SHA-256:
`fe6a06fcc4d3951ff741b7b3d8bdf819507d292bf6d1e4b65c60717348bbeced`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open MvPolynomial
universe u


namespace MvPolynomial

variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pullback coordinates. The corresponding scheme map goes translated → original. -/
def shiftCoordinates (r t : k) : Fin 3 → MvPolynomial (Fin 3) k :=
  ![MvPolynomial.X 0 + MvPolynomial.C r * MvPolynomial.X 2,
    MvPolynomial.X 1 + MvPolynomial.C t * MvPolynomial.X 2, MvPolynomial.X 2]

def shiftPolynomial (r t : k) : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (shiftCoordinates r t)

@[simp] lemma shiftPolynomial_C (r t a : k) :
    shiftPolynomial r t (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [shiftPolynomial]

@[simp] lemma shiftPolynomial_X (r t : k) (i : Fin 3) :
    shiftPolynomial r t (MvPolynomial.X i) = shiftCoordinates r t i := by
  simp [shiftPolynomial]

lemma shiftCoordinates_homogeneous (r t : k) (i : Fin 3) :
    (shiftCoordinates r t i).IsHomogeneous 1 := by
  fin_cases i
  · exact (isHomogeneous_X k 0).add ((isHomogeneous_X k 2).C_mul r)
  · exact (isHomogeneous_X k 1).add ((isHomogeneous_X k 2).C_mul t)
  · exact isHomogeneous_X k 2

lemma shiftPolynomial_homogeneous (r t : k) {n : ℕ}
    {p : MvPolynomial (Fin 3) k} (hp : p.IsHomogeneous n) :
    (shiftPolynomial r t p).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C (shiftCoordinates r t) p).IsHomogeneous n
  simpa only [one_mul] using hp.eval₂ MvPolynomial.C (shiftCoordinates r t)
    (fun a => isHomogeneous_C _ a) (shiftCoordinates_homogeneous r t)

lemma shiftPolynomial_comp (r t r' t' : k) :
    (shiftPolynomial r t).comp (shiftPolynomial r' t') =
      shiftPolynomial (r + r') (t + t') := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [shiftCoordinates, map_add, map_mul] <;> ring

lemma shiftPolynomial_zero : shiftPolynomial (0 : k) 0 = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    fin_cases i <;> simp [shiftCoordinates]

lemma shiftPolynomial_inverse (r t : k) (p : MvPolynomial (Fin 3) k) :
    shiftPolynomial (-r) (-t) (shiftPolynomial r t p) = p := by
  have h := shiftPolynomial_comp (-r) (-t) r t
  rw [neg_add_cancel, neg_add_cancel, shiftPolynomial_zero] at h
  exact DFunLike.congr_fun h p

lemma shiftPolynomial_inverse' (r t : k) (p : MvPolynomial (Fin 3) k) :
    shiftPolynomial r t (shiftPolynomial (-r) (-t) p) = p := by
  simpa using shiftPolynomial_inverse (-r) (-t) p

end MvPolynomial
