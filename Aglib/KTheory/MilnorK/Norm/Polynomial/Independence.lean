/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.SylowInduction

/-!
# General polynomial-presentation independence in characteristic zero

Strong induction runs over all characteristic-zero fields at a fixed Milnor
degree. Restriction to every finite Sylow fixed field reduces all actual scalar
branches to the proved p-group step. The degree retractions jointly detect the
original difference. No canonical norm, general tower law, or independence
premise is assumed by the final theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

universe u

/-- Actual polynomial norms are independent of the polynomial presentation,
for every Milnor degree over every characteristic-zero field. -/
theorem polynomialNorm_map_algEquiv
    {k : Type u} [Field k] [CharZero k] (n : ℕ)
    (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x := by
  classical
  have main : ∀ d : ℕ, ∀ (A : Type u) [Field A] [CharZero A]
      (r s : MonicIrreducible A), r.val.natDegree = d →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[A] AdjoinRoot s.val) (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A _ _ r s hdeg ε y
      let Ω := r.val.SplittingField
      let : IsGalois A Ω := ⟨⟩
      apply eq_of_sylow_restrictions A Ω n
      intro ℓ hℓ
      let : Fact ℓ.Prime := ⟨hℓ⟩
      let S : Sylow ℓ (Ω ≃ₐ[A] Ω) := Classical.arbitrary _
      refine ⟨S, ?_⟩
      apply polynomialNorm_restrict_map_algEquiv_of_pGroup_of_lower_degrees
        (Ω := Ω) ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ S)
        n d r s hdeg.le ε (SplittingField.splits r.val) ?_ y
      intro B _ _ a b ha η z
      exact ih a.val.natDegree ha B a b rfl η z
  exact main p.val.natDegree k p q rfl e x

/-- Presentation independence as an equality of the original integer-linear maps. -/
theorem polynomialNorm_comp_map_algEquiv
    {k : Type u} [Field k] [CharZero k] (n : ℕ)
    (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) :
    (polynomialNorm n q).comp (map n e.toRingHom) = polynomialNorm n p := by
  apply LinearMap.ext
  exact polynomialNorm_map_algEquiv n p q e

end MilnorK.PolynomialNorm
