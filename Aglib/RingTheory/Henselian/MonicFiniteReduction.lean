/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Monic finite reduction at a closed point

For a finitely generated field algebra, monic positive-degree equations for the
residue coordinates define an actual polynomial algebra action. The original
generators are integral for this action, so the algebra is module-finite, and
the selected prime contracts to the polynomial origin. The action need not be
injective; no residue separability is used.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonicFiniteReduction

variable {F : Type u} [Field F] {B : Type v} [CommRing B] [Algebra F B]
variable {n : ℕ} (z : Fin n → B) (Q : Fin n → Polynomial F)

/-- The actual polynomial map used in the closed-point finite reduction. -/
def polynomialMap : MvPolynomial (Fin n) F →ₐ[F] B :=
  MvPolynomial.aeval (fun i => Polynomial.aeval (z i) (Q i))

/-- No injectivity of this polynomial algebra action is asserted or needed. -/
abbrev polynomialAlgebra : Algebra (MvPolynomial (Fin n) F) B :=
  (polynomialMap z Q).toRingHom.toAlgebra

/-- Monic equations turn the original finite algebra generators into integral
ones for the new, possibly nonfaithful, polynomial algebra action. -/
theorem finite (hz : Algebra.adjoin F (Set.range z) = ⊤)
    (hmonic : ∀ i, (Q i).Monic) (hdegree : ∀ i, 0 < (Q i).natDegree) :
    let := polynomialAlgebra z Q
    Module.Finite (MvPolynomial (Fin n) F) B := by
  let := polynomialAlgebra z Q
  let : IsScalarTower F (MvPolynomial (Fin n) F) B :=
    IsScalarTower.of_algHom (polynomialMap z Q)
  have hint (i : Fin n) : IsIntegral (MvPolynomial (Fin n) F) (z i) := by
    refine ⟨(Q i).map (algebraMap F (MvPolynomial (Fin n) F)) -
      Polynomial.C (MvPolynomial.X i), ?_, ?_⟩
    · apply ((hmonic i).map _).sub_of_left
      apply lt_of_le_of_lt Polynomial.degree_C_le
      rw [(hmonic i).degree_map]
      exact Polynomial.natDegree_pos_iff_degree_pos.mp (hdegree i)
    · change Polynomial.aeval (z i) ((Q i).map (algebraMap F (MvPolynomial (Fin n) F)) -
        Polynomial.C (MvPolynomial.X i)) = 0
      rw [map_sub, Polynomial.aeval_C, Polynomial.aeval_map_algebraMap]
      change Polynomial.aeval (z i) (Q i) - polynomialMap z Q (MvPolynomial.X i) = 0
      simp [polynomialMap]
  have hz' : Algebra.adjoin (MvPolynomial (Fin n) F) (Set.range z) = ⊤ := by
    apply eq_top_iff.mpr
    intro b hb
    have hle : Algebra.adjoin F (Set.range z) ≤
        (Algebra.adjoin (MvPolynomial (Fin n) F) (Set.range z)).restrictScalars F := by
      apply Algebra.adjoin_le
      intro x hx
      exact Algebra.subset_adjoin (R := MvPolynomial (Fin n) F) hx
    apply hle
    rw [hz]
    trivial
  rw [Module.finite_def]
  simpa only [hz', Algebra.top_toSubmodule] using
    (fg_adjoin_of_finite (R := MvPolynomial (Fin n) F) (Set.finite_range z)
      (by rintro _ ⟨i, rfl⟩; exact hint i))

/-- The selected prime contracts to the actual polynomial-origin ideal. -/
theorem comap_eq_origin (q : Ideal B) [q.IsPrime]
    (hQ : ∀ i, Polynomial.aeval (z i) (Q i) ∈ q) :
    q.comap (polynomialMap z Q).toRingHom = PolynomialLocalRing.originIdeal F n := by
  have hmaps : (Ideal.Quotient.mk q).comp (polynomialMap z Q).toRingHom =
      (algebraMap F (B ⧸ q)).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [polynomialMap]
    · intro i
      simpa [polynomialMap, Ideal.Quotient.eq_zero_iff_mem] using hQ i
  ext p
  change polynomialMap z Q p ∈ q ↔ MvPolynomial.constantCoeff p ∈ IsLocalRing.maximalIdeal F
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ((Ideal.Quotient.mk q).comp (polynomialMap z Q).toRingHom) p = 0 ↔ _
  rw [hmaps]
  exact (algebraMap F (B ⧸ q)).injective.eq_iff' (map_zero _)

end MonicFiniteReduction
