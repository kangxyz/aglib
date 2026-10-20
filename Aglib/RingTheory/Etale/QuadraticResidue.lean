/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.QuadraticDVR

/-!
# Roots and irreducibility of quadratic residue polynomials

General declarations relocated from R5 baseline
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; names, maps and hypotheses unchanged.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/QuadraticResidue.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0fb3f1525434e77ebe3f773f9e597ccfe3e583722b1d9f5599d0ca3a900e02e1`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open Polynomial IsLocalRing
namespace Algebra.QuadraticEtale
variable {R : Type u} [CommRing R]

lemma simple_root_of_unit_discriminant [IsLocalRing R] (a b : R)
    (hd : IsUnit (a ^ 2 + 4 * b)) (s : ResidueField R)
    (hs : s ^ 2 + residue R a * s - residue R b = 0) :
    2 * s + residue R a ≠ 0 := by
  have hd' := (residue_ne_zero_iff_isUnit (a ^ 2 + 4 * b)).mpr hd
  have he : (2 * s + residue R a) ^ 2 = residue R (a ^ 2 + 4 * b) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hs
  intro hz
  rw [hz, zero_pow (by decide)] at he
  exact hd' he.symm

lemma residue_polynomial_irreducible [IsLocalRing R] (a b : R)
    (hno : ¬ ∃ s : ResidueField R, s ^ 2 + residue R a * s - residue R b = 0) :
    Irreducible ((polynomial a b).map (residue R)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [(polynomial_monic a b).natDegree_map, polynomial_natDegree]
    decide
  · intro x hx
    apply hno
    refine ⟨x, ?_⟩
    change (((X : R[X]) ^ 2 + C a * X - C b).map (residue R)).eval x = 0 at hx
    simpa only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hx

end Algebra.QuadraticEtale
