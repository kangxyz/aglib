/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeTower
public import Aglib.RingTheory.AdjoinRootTowerBranchChange

/-!
# Presentation-independence induction through an actual normal-prime subfield

The induction premise concerns only strictly smaller polynomial degrees over
the actual lower root field. The proved normal-prime tower and the constructed
relative presentation equivalence then compare the original upper norms.
This is a genuine induction step, not an unconditional independence theorem.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

/-- Actual lower-degree presentation independence suffices when the upper field
contains a normal-prime subfield. All relative presentations are constructed. -/
theorem polynomialNorm_map_algEquiv_of_prime_subfield_of_lower_degrees
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h₁ h₂ : MonicIrreducible k)
    (e : AdjoinRoot h₁.val ≃ₐ[k] AdjoinRoot h₂.val)
    (f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h₁.val) (n : ℕ)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < h₁.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot h₁.val) n) :
    polynomialNorm n h₂ (map n e.toRingHom x) = polynomialNorm n h₁ x := by
  let q₁ := AdjoinRoot.towerBranch p.val h₁.val f
  let q₂ := AdjoinRoot.towerBranch p.val h₂.val (e.toAlgHom.comp f)
  let ε := AdjoinRoot.towerBranchChangeAlgEquiv p.val h₁.val h₂.val e f
  have hd : q₁.val.val.natDegree < h₁.val.natDegree :=
    AdjoinRoot.towerBranch_natDegree_lt p.val h₁.val p.property.1 h₁.property.1 hp.one_lt f
  rw [polynomialNorm_eq_prime_tower p hp h₂ (e.toAlgHom.comp f),
    polynomialNorm_eq_prime_tower p hp h₁ f]
  apply congrArg (polynomialNorm n p)
  have hsquare := congrArg (map n)
    (AdjoinRoot.towerBranchChangeAlgEquiv_comp_adjoinRootMap p.val h₁.val h₂.val e f)
  rw [map_comp, map_comp] at hsquare
  have hx := LinearMap.congr_fun hsquare x
  change map n ε.toRingHom
      (map n (adjoinRootMap (algebraMap k (AdjoinRoot p.val)) h₁.val
        q₁.val.val q₁.property) x) =
    map n (adjoinRootMap (algebraMap k (AdjoinRoot p.val)) h₂.val
      q₂.val.val q₂.property) (map n e.toRingHom x) at hx
  rw [← hx]
  exact ih q₁.val q₂.val hd ε _

end MilnorK.PolynomialNorm
