/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationPolynomialDescent
public import Aglib.RingTheory.Extension.Presentation.PolynomialSystem
public import Aglib.RingTheory.Localization.PolynomialSystem

/-!
# Eliminating henselized coefficients by auxiliary variables

A polynomial system with finitely many equations over the henselization of a
localization is encoded over the ring before localization. Its finitely many
coefficients descend to one pointed etale neighborhood, whose finite
presentation supplies auxiliary equations. A common actual unit denominator clears all localized
coefficients. Residue agreement forces the auxiliary coordinates to be the
original stage point, so solutions solve the original system, not a system
with merely nearby coefficients. No approximation property or Jacobian rank
claim is part of this coefficient reduction.
-/

@[expose] public section

noncomputable section

open MvPolynomial IsLocalRing

universe u v w₁ w₂ t

namespace Henselization

/-- A system with finitely many equations over a henselized localization is
encoded over the original ring with finitely many auxiliary unknowns and
relations. The ambient unknown index may be arbitrary. The same equations
extend original points in every local target, and near the fixed auxiliary
coordinates their solutions solve the original system with its original coefficients. -/
theorem exists_polynomial_system_before_localization
    {A : Type u} {L : Type v} {σ : Type w₁} {ι : Type w₂}
    [CommRing A] [CommRing L] [Algebra A L] [IsLocalRing L]
    (M : Submonoid A) [IsLocalization M L] [Finite ι]
    (F : ι → MvPolynomial σ (Henselization L)) :
    ∃ (n m : ℕ) (E : (ι ⊕ Fin m) → MvPolynomial (σ ⊕ Fin n) A)
      (z₀ : Fin n → Henselization L),
      ∀ (T : Type t) [CommRing T] [Algebra L T] [IsLocalRing T]
        (f : Henselization L →ₐ[L] T) (y : σ → T),
      ((∀ k, eval₂ ((algebraMap L T).comp (algebraMap A L))
          (Sum.elim y (fun j => f (z₀ j))) (E k) = 0) ↔
        ∀ i, eval₂ f.toRingHom y (F i) = 0) ∧
      (∀ z : Fin n → T,
        (∀ k, eval₂ ((algebraMap L T).comp (algebraMap A L))
          (Sum.elim y z) (E k) = 0) →
        (∀ j, z j - f (z₀ j) ∈ maximalIdeal T) →
        (∀ j, z j = f (z₀ j)) ∧ ∀ i, eval₂ f.toRingHom y (F i) = 0) := by
  obtain ⟨S, G, hG⟩ := exists_mvPolynomial_family_rep L F
  obtain ⟨n, m, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin L S.algebra
  obtain ⟨D, hD⟩ := P.exists_polynomial_system_over_base G
  obtain ⟨s, E, _, hE⟩ :=
    IsLocalization.exists_common_denominator_polynomial_system M D
  refine ⟨n, m, E, (fun j => Henselization.ι L S (P.val j)), ?_⟩
  intro T _ _ _ f y
  have hpoint := hD T (f.comp (Henselization.ι L S)) y
  have horiginal (i : ι) :
      eval₂ (f.comp (Henselization.ι L S)).toRingHom y (G i) = eval₂ f.toRingHom y (F i) := by
    rw [← hG i, eval₂_map]
    rfl
  have hclear (z : Fin n → T) :
      (∀ k, eval₂ ((algebraMap L T).comp (algebraMap A L)) (Sum.elim y z)
        (E k) = 0) ↔ ∀ k, eval₂ (algebraMap L T) (Sum.elim y z) (D k) = 0 := by
    exact forall_congr' (fun k => hE T (algebraMap L T) (Sum.elim y z) k)
  constructor
  · rw [hclear]
    exact hpoint.1.trans (forall_congr' (fun i => by rw [horiginal i]))
  · intro z hz hclose
    obtain ⟨hzfixed, hzero⟩ := hpoint.2 z ((hclear z).mp hz) hclose
    refine ⟨hzfixed, fun i => ?_⟩
    exact (horiginal i).symm.trans (hzero i)

end Henselization
