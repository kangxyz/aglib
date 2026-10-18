/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeInduction
public import Aglib.KTheory.MilnorK.Norm.Polynomial.PGroupInduction
public import Aglib.KTheory.MilnorK.RestrictionSylow
public import Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding

/-!
# Actual Sylow restriction comparison in strong degree induction

All scalar branches embed into the specified p-group Galois ambient. Their
norms are compared by the proved normal-prime tower step and only strictly
smaller-degree presentation independence. Every branch and original map is kept.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue AdjoinRoot

universe u

/-- The actual branch formula compares restrictions in a p-group splitting
ambient under the explicit strong-induction hypothesis. -/
theorem polynomialNorm_restrict_map_algEquiv_of_pGroup_of_lower_degrees
    {k L Ω : Type u} [Field k] [CharZero k] [Field L] [Field Ω]
    [Algebra k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (n d : ℕ) (p q : MonicIrreducible k) (hd : p.val.natDegree ≤ d)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (hsplit : (p.val.map (algebraMap k Ω)).Splits)
    (ih : ∀ (A : Type u) [Field A] [CharZero A] (r s : MonicIrreducible A),
      r.val.natDegree < d → ∀ (ε : AdjoinRoot r.val ≃ₐ[A] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (MilnorK.map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    MilnorK.map n (algebraMap k L)
        (polynomialNorm n q (MilnorK.map n e.toRingHom x)) =
      MilnorK.map n (algebraMap k L) (polynomialNorm n p x) := by
  classical
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let φ := algebraMap k L
  let hp' : p.val.map φ ≠ 0 := Polynomial.map_ne_zero p.property.2.ne_zero
  let hq' : q.val.map φ ≠ 0 := Polynomial.map_ne_zero q.property.2.ne_zero
  let E := coefficientEquiv (L := L) e
  let B := (placesAboveBranchEquiv φ p).trans
    ((polynomialBranchEquiv _ _ hp' hq' E).trans (placesAboveBranchEquiv φ q).symm)
  rw [polynomialNorm_restrict, polynomialNorm_restrict]
  simp only [Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv B
  intro r
  let rb : IrreducibleBranch (p.val.map φ) := placesAboveBranchEquiv φ p r
  let ε : AdjoinRoot r.val.val ≃ₐ[L] AdjoinRoot (B r).val.val :=
    polynomialBranchAlgEquiv _ _ hp' hq' E rb
  have hdeg : r.val.val.natDegree ≤ d := by
    have hle := natDegree_le_of_dvd rb.property (Polynomial.map_ne_zero p.property.2.ne_zero)
    rw [natDegree_map] at hle
    exact hle.trans hd
  obtain ⟨⟨g⟩, _⟩ := AdjoinRoot.nonempty_algHom_branch_of_splits p.val
    p.property.2.ne_zero hsplit rb
  have hsquare : ε.toRingHom.comp
      (adjoinRootMap φ p.val r.val.val ((mem_placesAbove φ p r.val).mp r.property)) =
      (adjoinRootMap φ q.val (B r).val.val
        ((mem_placesAbove φ q (B r).val).mp (B r).property)).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact scalarBranchAlgEquiv_adjoinRootMap p.val q.val e rb a
  have hmaps : MilnorK.map n ε.toRingHom
      (MilnorK.map n
        (adjoinRootMap φ p.val r.val.val ((mem_placesAbove φ p r.val).mp r.property)) x) =
      MilnorK.map n (adjoinRootMap φ q.val (B r).val.val
        ((mem_placesAbove φ q (B r).val).mp (B r).property))
          (MilnorK.map n e.toRingHom x) := by
    simpa only [MilnorK.map_comp, LinearMap.comp_apply] using
      congrArg (fun g => MilnorK.map n g x) hsquare
  exact (polynomialNorm_map_algEquiv_of_pGroup_of_lower_degrees ℓ hG n d
    r.val (B r).val hdeg ε g ih _).symm.trans
    (congrArg (polynomialNorm n (B r).val) hmaps)

end MilnorK.PolynomialNorm
