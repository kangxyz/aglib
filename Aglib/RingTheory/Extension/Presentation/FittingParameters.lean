/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.Parameters
public import Aglib.RingTheory.Extension.Presentation.Fitting

/-! # The two Fitting bounds for a coordinate projection

Absorbing d parameter coordinates changes the relative Fitting index from k to k-d.
The projected ideal is contained in the original ideal. Equality after evaluation
follows when a retained minor generates the evaluated original ideal; no principality
of the original ideal in the source algebra is asserted.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Presentation

variable {R B α β σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [Algebra (MvPolynomial α R) B] [IsScalarTower R (MvPolynomial α R) B]
variable [Finite α] [Finite β]

set_option backward.isDefEq.respectTransparency false in
/-- Absorbing d polynomial parameters yields the intrinsic projected-to-original
Fitting inclusion, with the relative index decreased by d. -/
theorem fittingIdeal_absorbPolynomialParameters_le
    (P : Presentation R B (β ⊕ α) σ)
    (ha : ∀ i, algebraMap (MvPolynomial α R) B (X i) = P.val (.inr i))
    (k : ℕ) (hk : Nat.card α ≤ k) :
    Module.fittingIdeal B (KaehlerDifferential (MvPolynomial α R) B) (k - Nat.card α) ≤
      Module.fittingIdeal B (KaehlerDifferential R B) k := by
  let Q := P.absorbPolynomialParameters ha
  have hc : Nat.card β - (k - Nat.card α) = Nat.card (β ⊕ α) - k := by
    rw [Nat.card_sum]
    omega
  rw [Q.fittingIdeal_kaehler_eq_minorIdeal, P.fittingIdeal_kaehler_eq_minorIdeal, ← hc]
  apply Ideal.span_le.mpr
  rintro _ ⟨e, c, rfl⟩
  apply Ideal.subset_span
  refine ⟨Sum.inl ∘ e, c, ?_⟩
  apply congrArg Matrix.det
  ext i j
  exact (P.toGenerators.aeval_pderiv_absorbPolynomialParameters ha
    (P.relation (c j)) (e i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- A retained minor generating the evaluated original Fitting ideal proves equality
only after that evaluation. Choosing projection coordinates with this property is a
separate geometric assertion. -/
theorem map_fittingIdeal_absorbPolynomialParameters_eq_of_retained_minor
    {S : Type*} [CommRing S] (P : Presentation R B (β ⊕ α) σ)
    (ha : ∀ i, algebraMap (MvPolynomial α R) B (X i) = P.val (.inr i))
    (k : ℕ) (hk : Nat.card α ≤ k) (χ : B →+* S)
    (e : Fin (Nat.card β - (k - Nat.card α)) → β)
    (c : Fin (Nat.card β - (k - Nat.card α)) → σ)
    (hselected : Ideal.span {χ (Matrix.of fun i j =>
      aeval P.val (pderiv (.inl (e i)) (P.relation (c j)))).det} =
        (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ) :
    (Module.fittingIdeal B (KaehlerDifferential (MvPolynomial α R) B)
      (k - Nat.card α)).map χ =
        (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ := by
  apply le_antisymm (Ideal.map_mono (P.fittingIdeal_absorbPolynomialParameters_le ha k hk))
  rw [← hselected]
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  let Q := P.absorbPolynomialParameters ha
  let D : Matrix _ _ B := fun i j => aeval Q.val (pderiv (e i) (Q.relation (c j)))
  have hm : D.det ∈
      Module.fittingIdeal B (KaehlerDifferential (MvPolynomial α R) B)
        (k - Nat.card α) := by
    rw [Q.fittingIdeal_kaehler_eq_minorIdeal]
    exact Ideal.subset_span ⟨e, c, rfl⟩
  have he : D = Matrix.of (fun i j =>
      aeval P.val (pderiv (.inl (e i)) (P.relation (c j)))) := by
    ext i j
    exact P.toGenerators.aeval_pderiv_absorbPolynomialParameters ha
      (P.relation (c j)) (e i)
  rw [he] at hm
  exact Ideal.mem_map_of_mem χ hm

end Algebra.Presentation
