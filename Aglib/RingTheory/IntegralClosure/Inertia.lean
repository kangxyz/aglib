/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Actual decomposition and inertia groups of a DVR

The integral model is the integral closure of a genuine DVR in the fixed
algebraic closure of its fraction field. A maximal ideal above the DVR's
maximal ideal exists by lying over. Its stabilizer is the decomposition
group, and the subgroup acting identically modulo that ideal is inertia.
Their topologies are inherited from the actual Krull topology. Restriction
on continuous H¹ is induced by the continuous subgroup inclusion.
-/

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e34f96c48f50feeef88e86fdd41ac6485696a3bfd841a18209a34fb11524fb53`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
namespace integralClosure.Inertia

open scoped Pointwise
open Field.absoluteGaloisGroup.RootsOfUnity


variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

local instance closureGaloisAction :
    MulSemiringAction (Field.absoluteGaloisGroup K) (AlgebraicClosure K) :=
  inferInstanceAs (MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K))

local instance closureGaloisComm :
    SMulCommClass (Field.absoluteGaloisGroup K) R (AlgebraicClosure K) :=
  inferInstanceAs (SMulCommClass
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) R (AlgebraicClosure K))

/-- The actual integral closure of the DVR in its fraction field's algebraic closure. -/
abbrev IntegralModel := integralClosure R (AlgebraicClosure K)

instance integralModelAction :
    MulSemiringAction (Field.absoluteGaloisGroup K) (IntegralModel R K) :=
  inferInstanceAs (MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (integralClosure R (AlgebraicClosure K)))

/-- The decomposition subgroup is the stabilizer of the actual prime ideal. -/
abbrev decomposition (Q : Ideal (IntegralModel R K)) : Subgroup (Field.absoluteGaloisGroup K) :=
  MulAction.stabilizer (Field.absoluteGaloisGroup K) Q

/-- Actual inertia: Galois automorphisms inducing the identity modulo `Q`. -/
abbrev inertia (Q : Ideal (IntegralModel R K)) : Subgroup (Field.absoluteGaloisGroup K) :=
  Q.inertia (Field.absoluteGaloisGroup K)

/-- Membership is the literal residue-triviality condition. -/
theorem mem_inertia_iff (Q : Ideal (IntegralModel R K)) (g : Field.absoluteGaloisGroup K) :
    g ∈ inertia R K Q ↔ ∀ x : IntegralModel R K, g • x - x ∈ Q :=
  Ideal.mem_inertia

/-- Residue-trivial automorphisms preserve the chosen prime. -/
theorem inertia_le_decomposition (Q : Ideal (IntegralModel R K)) :
    inertia R K Q ≤ decomposition R K Q := Ideal.inertia_le_stabilizer Q

/-- The subgroup inclusion is continuous for the inherited Krull topology. -/
def inclusion (Q : Ideal (IntegralModel R K)) :
    ContinuousMonoidHom (inertia R K Q) (Field.absoluteGaloisGroup K) where
  toMonoidHom := (inertia R K Q).subtype
  continuous_toFun := continuous_subtype_val

@[simp] theorem inclusion_apply (Q : Ideal (IntegralModel R K)) (g : inertia R K Q) :
    inclusion R K Q g = g.val := rfl

/-- Distinct roots of unity remain distinct modulo a prime away from their order.
The proof uses the factorization of a difference of powers and its reduction. -/
theorem root_eq_of_residue_eq {D : Type*} [CommRing D] [IsDomain D]
    (Q : Ideal D) [Q.IsPrime] (n : ℕ) (hn : (n : D) ∉ Q)
    {x y : D} (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y) : x = y := by
  by_contra hne
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (by simp)
  have hs : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = 0 := by
    have h := geom_sum₂_mul x y n
    rw [hx, hy, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hs' := congrArg (Ideal.Quotient.mk Q) hs
  rw [RingHom.map_geom_sum₂, hxy, geom_sum₂_self, map_zero] at hs'
  have hn' : (n : D ⧸ Q) ≠ 0 := by
    intro h
    apply hn
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using h
  have hy' : Ideal.Quotient.mk Q y ≠ 0 := by
    apply IsUnit.ne_zero
    exact (IsUnit.of_pow_eq_one hy hn0).map (Ideal.Quotient.mk Q)
  exact (mul_ne_zero hn' (pow_ne_zero _ hy')) hs'

/-- Roots of unity are integral over the DVR, with no chosen primitive root. -/
def rootElement (n : ℕ) (hn : 0 < n) (ζ : Mu K n) : IntegralModel R K := by
  refine ⟨((ζ.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K), ?_⟩
  apply IsIntegral.of_pow hn
  have hp : (((ζ.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ n = 1 := by
    have h := (mem_rootsOfUnity n (ζ.toMul : (AlgebraicClosure K)ˣ)).mp ζ.toMul.property
    exact congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) h
  rw [hp]
  exact isIntegral_one

@[simp] theorem rootElement_pow (n : ℕ) (hn : 0 < n) (ζ : Mu K n) :
    rootElement R K n hn ζ ^ n = 1 := by
  apply Subtype.ext
  exact congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K))
    ((mem_rootsOfUnity n _).mp ζ.toMul.property)

/-- The embedding of actual roots into the integral model respects Galois action. -/
theorem rootElement_smul (n : ℕ) (hn : 0 < n) (ζ : Mu K n)
    (g : Field.absoluteGaloisGroup K) :
    rootElement R K n hn (g • ζ) = g • rootElement R K n hn ζ := by
  apply Subtype.ext
  rfl

/-- Inertia fixes all roots whose order is invertible in the DVR. -/
theorem inertia_fixes_roots (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (ζ : Mu K n) (g : inertia R K Q) :
    (g.val : Field.absoluteGaloisGroup K) • ζ = ζ := by
  have hnB : IsUnit (n : IntegralModel R K) := by
    simpa using hnunit.map (algebraMap R (IntegralModel R K))
  have hres : Ideal.Quotient.mk Q (g.val • rootElement R K n hn ζ) =
      Ideal.Quotient.mk Q (rootElement R K n hn ζ) :=
    Ideal.Quotient.eq.mpr ((mem_inertia_iff R K Q g.val).mp g.property _)
  have heq := root_eq_of_residue_eq Q n (Ideal.notMem_of_isUnit Q hnB)
    (show (g.val • rootElement R K n hn ζ) ^ n = 1 by
      rw [← smul_pow', rootElement_pow, smul_one])
    (rootElement_pow R K n hn ζ) hres
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun z : IntegralModel R K => (z : AlgebraicClosure K)) heq

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

instance integralModelFaithful : FaithfulSMul R (IntegralModel R K) := by
  apply (faithfulSMul_iff_algebraMap_injective R (IntegralModel R K)).mpr
  intro x y h
  have h' := congrArg (fun z : IntegralModel R K => (z : AlgebraicClosure K)) h
  exact (algebraMap K (AlgebraicClosure K)).injective
    |>.comp (IsFractionRing.injective R K) |>.eq_iff.mp h'

/-- Lying over supplies a genuine maximal ideal above the DVR closed point. -/
theorem exists_maximal_above :
    ∃ Q : Ideal (IntegralModel R K), Q.IsMaximal ∧ Q.LiesOver (IsLocalRing.maximalIdeal R) :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral (IsLocalRing.maximalIdeal R)

/-- A selected actual extension of the closed point, not arbitrary group data. -/
def chosenPrime : Ideal (IntegralModel R K) := (exists_maximal_above R K).choose

instance chosenPrimeMaximal : (chosenPrime R K).IsMaximal :=
  (exists_maximal_above R K).choose_spec.1

instance chosenPrimeLiesOver : (chosenPrime R K).LiesOver (IsLocalRing.maximalIdeal R) :=
  (exists_maximal_above R K).choose_spec.2

/-- The chosen actual inertia subgroup. -/
abbrev chosenInertia := inertia R K (chosenPrime R K)

variable (Q : Ideal (IntegralModel R K)) [Q.IsMaximal]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]

/-- The actual decomposition-group action on the residue extension. -/
def residueAction : decomposition R K Q →*
    ((IntegralModel R K ⧸ Q) ≃ₐ[R ⧸ IsLocalRing.maximalIdeal R] (IntegralModel R K ⧸ Q)) :=
  Ideal.Quotient.stabilizerHom Q (IsLocalRing.maximalIdeal R) (Field.absoluteGaloisGroup K)

omit [IsFractionRing R K] [Q.IsMaximal] in
/-- Inertia is exactly the residue-action kernel, viewed inside the absolute Galois group. -/
theorem inertia_eq_residue_kernel :
    inertia R K Q = (residueAction R K Q).ker.map (decomposition R K Q).subtype :=
  (Ideal.Quotient.map_ker_stabilizer_subtype Q (IsLocalRing.maximalIdeal R)
    (Field.absoluteGaloisGroup K)).symm

end DVR
end integralClosure.Inertia
