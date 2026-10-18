/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.PGroupNormalPrimePresentation
public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeSubfieldInduction

/-!
# The p-group ambient step of polynomial norm strong induction

Every nontrivial root field in a finite Galois p-group ambient has an actual
normal-prime subfield. The proved tower reduces comparison to strictly smaller
relative degrees. The induction hypothesis below is explicitly all smaller
degrees over all characteristic-zero fields, at the same fixed Milnor degree.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open MilnorK.K3.PolynomialNorm (rootEvaluation rootEvaluationEquiv
  rootEvaluationEquiv_symm_toRingHom rootEvaluation_algebraMap)

universe u

/-- Linear presentations have identical actual norms under their original
base-field equivalence, in every characteristic and every Milnor degree. -/
theorem polynomialNorm_map_algEquiv_of_degree_one
    {k : Type u} [Field k] (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree = 1) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x := by
  have hq : q.val.natDegree = 1 := (natDegree_eq_of_root_algEquiv p q e).symm.trans hp
  rw [polynomialNorm_eq_map_rootEvaluation n p hp,
    polynomialNorm_eq_map_rootEvaluation n q hq]
  have he : (rootEvaluation q hq).comp e.toRingHom = rootEvaluation p hp := by
    apply RingHom.ext
    intro a
    obtain ⟨b, rfl⟩ := (rootEvaluationEquiv p hp).symm.surjective a
    change rootEvaluation q hq (e ((rootEvaluationEquiv p hp).symm.toRingHom b)) =
      rootEvaluation p hp ((rootEvaluationEquiv p hp).symm.toRingHom b)
    rw [rootEvaluationEquiv_symm_toRingHom, AlgEquiv.commutes,
      rootEvaluation_algebraMap, rootEvaluation_algebraMap]
  rw [← LinearMap.comp_apply, ← map_comp, he]

/-- The actual p-group ambient supplies the normal-prime subfield; the only
norm premise is presentation independence in strictly smaller degrees. -/
theorem polynomialNorm_map_algEquiv_of_pGroup_of_lower_degrees
    {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
    [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
    (n d : ℕ) (p q : MonicIrreducible k) (hd : p.val.natDegree ≤ d)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (g : AdjoinRoot p.val →ₐ[k] Ω)
    (ih : ∀ (L : Type u) [Field L] [CharZero L] (r s : MonicIrreducible L),
      r.val.natDegree < d → ∀ (ε : AdjoinRoot r.val ≃ₐ[L] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x := by
  by_cases hp : p.val.natDegree = 1
  · exact polynomialNorm_map_algEquiv_of_degree_one n p q hp e x
  have hp1 : 1 < p.val.natDegree := by
    have hpos := p.property.2.natDegree_pos
    omega
  let : FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
  have hdim : 1 < Module.finrank k (AdjoinRoot p.val) := by
    simpa only [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim] using hp1
  obtain ⟨r, hrnormal, hrdegree, ⟨f⟩⟩ :=
    exists_normal_prime_presentation_of_isPGroup_embedding ℓ hG g hdim
  let : Normal k (AdjoinRoot r.val) := hrnormal
  let : CharZero (AdjoinRoot r.val) :=
    charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot r.val)).injective
  apply polynomialNorm_map_algEquiv_of_prime_subfield_of_lower_degrees r
    (hrdegree ▸ (Fact.out : ℓ.Prime)) p q e f n ?_ x
  intro a b ha ε y
  exact ih (AdjoinRoot r.val) a b (ha.trans_le hd) ε y

end MilnorK.PolynomialNorm
