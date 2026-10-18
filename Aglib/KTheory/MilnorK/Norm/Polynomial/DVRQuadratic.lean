/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.DVRUniformizer
public import Aglib.KTheory.MilnorK.MixedGeneration

/-!
# All-class quadratic polynomial-norm residue compatibility

The prime-degree mixed square extends by integer linearity to the actual mixed
span. In quadratic degree the already proved mixed-generation theorem identifies
this span with the entire Milnor group, in every positive Milnor degree.
All DVR, Henselian, residue-characteristic and presentation hypotheses are
retained. No general canonical norm, tower law or curve reciprocity is asserted.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [HenselianLocalRing S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [CharZero (ResidueField R)]
  [Algebra S (AdjoinRoot p.val)] [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]

/-- The genuine prime-degree square holds on the integer span of mixed symbols,
not merely on a single decomposable symbol or a chosen prefix class. -/
theorem residue_polynomialNorm_of_mem_mixedSpan (n : ℕ)
    (z : K (AdjoinRoot p.val) (n + 1))
    (hz : z ∈ mixedSpan (algebraMap F (AdjoinRoot p.val)) n)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime p.val.natDegree)
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p z) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n z)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, rfl⟩ := hy
    simpa only [MilnorK.map_symbol, productUnit_symbol, toMul_ofMul] using
      residue_polynomialNorm_mixed_prime R F p S n (symbol a) b
        hπ hϖ u e he heunit hp q ε
  | zero => simp only [map_zero]
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul a y _ hy => simp only [LinearMap.map_smul, hy]

/-- Every actual quadratic-extension class satisfies the selected
polynomial-presentation norm–residue square. The residue norm retains its
specified root-field equivalence. -/
theorem residue_polynomialNorm_quadratic (n : ℕ)
    (z : K (AdjoinRoot p.val) (n + 1)) (hp : p.val.natDegree = 2)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S))
    (q : MonicIrreducible (ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField S) :
    DVR.residue R F n (polynomialNorm (n + 1) p z) =
      polynomialNorm n q (map n ε.symm.toRingHom
        (DVR.residue S (AdjoinRoot p.val) n z)) := by
  apply residue_polynomialNorm_of_mem_mixedSpan R F p S n z _
    hπ hϖ u e he heunit (by rw [hp]; exact Nat.prime_two) q ε
  rw [mixedSpan_eq_top_of_natDegree_le_two p (by omega) n]
  trivial

end MilnorK.PolynomialNorm
