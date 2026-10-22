/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Generators
public import Aglib.RingTheory.MvPolynomial.ScaledTaylor
public import Mathlib.Tactic.Ring

/-! # Divided relations of the actual Néron modification

A relation whose value at the chosen centre is divisible by the scale gives a divided
relation in the actual new generating family. Cancellation takes place in the modification,
where the scale has already been proved regular, not in the original coefficient ring.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.NeronModification

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- Scaled Taylor expansion constructs a genuine divided relation in the kernel of the
new coordinates of the actual torsion-free modification. -/
theorem exists_divided_relation (P : Algebra.Generators R B ι) (p : R) (a : ι → R)
    (f : MvPolynomial ι R) (hf : f ∈ P.ker) (c : R) (hc : eval a f = p * c) :
    ∃ h Q : MvPolynomial ι R,
      Q ∈ (Ideal.span (Set.range (X : ι → MvPolynomial ι R))) ^ 2 ∧
      h = C c + (∑ j, C (eval a (pderiv j f)) * X j) + C p * Q ∧
      aeval (fun j => C (a j) + C p * X j) f = C p * h ∧
      h ∈ (coordinateGenerators P p a).ker := by
  classical
  obtain ⟨Q, hQ, hTaylor⟩ := exists_scaled_firstOrder_remainder f a p
    (X : ι → MvPolynomial ι R) (Ideal.span (Set.range X))
    (fun j => Ideal.subset_span ⟨j, rfl⟩)
  let h := C c + (∑ j, C (eval a (pderiv j f)) * X j) + C p * Q
  have hdiv : aeval (fun j => C (a j) + C p * X j) f = C p * h := by
    simp only [MvPolynomial.algebraMap_eq, hc, map_mul, map_pow] at hTaylor
    rw [hTaylor]
    dsimp [h]
    ring
  refine ⟨h, Q, hQ, rfl, hdiv, ?_⟩
  let g := fun j => P.val j - algebraMap R B (a j)
  let M := Modification (algebraMap R B p) g
  let z := coordinate (algebraMap R B p) g
  let E : MvPolynomial ι R →ₐ[R] M := aeval z
  let φ : B →ₐ[R] M := IsScalarTower.toAlgHom R B M
  have hcomp : E.comp (aeval fun j => C (a j) + C p * X j) =
      φ.comp (aeval P.val) := by
    ext j
    simp only [AlgHom.comp_apply, aeval_X, map_add, map_mul]
    change (aeval z) (C (a j)) + (aeval z) (C p) * (aeval z) (X j) = _
    rw [aeval_C, aeval_C, aeval_X]
    exact (of_generator_eq_center_add P p a j).symm
  have hfzero : aeval P.val f = 0 := by
    rwa [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker] at hf
  have hleft : E (aeval (fun j => C (a j) + C p * X j) f) = 0 := by
    have he := DFunLike.congr_fun hcomp f
    simpa only [AlgHom.comp_apply, hfzero, map_zero] using he
  have hp : IsRegular (algebraMap R M p) := by
    have hp' := isRegular_of (algebraMap R B p) g
    change IsRegular (algebraMap B M (algebraMap R B p)) at hp'
    rwa [← IsScalarTower.algebraMap_apply R B M p] at hp'
  have he := congrArg E hdiv
  rw [hleft, map_mul] at he
  have hEC : E (C p) = algebraMap R M p := aeval_C z p
  rw [hEC] at he
  have hz : E h = 0 := by
    apply hp.left
    simpa only [mul_zero] using he.symm
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
  exact hz

end Algebra.NeronModification
