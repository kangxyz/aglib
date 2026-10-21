/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.CharacterFactorization
public import Aglib.GroupCohomology.H1.Continuous.CocycleValues
public import Aglib.GroupCohomology.H1.Continuous.Hilbert90
public import Aglib.GroupCohomology.H1.Continuous.Inflation
public import Aglib.GroupCohomology.H1.Continuous.InnerConjugacy
public import Aglib.GroupCohomology.Kummer.InertiaConjugation
public import Aglib.GroupCohomology.Kummer.LocalInertia
public import Aglib.GroupCohomology.Kummer.RootAction
public import Aglib.GroupCohomology.Kummer.Surjectivity
public import Aglib.GroupCohomology.Kummer.TameSurjectivity

/-!
# Native clients of continuous character factorization and Kummer theory

The clients retain noncommutative groups, the zero character, independent ring
and field universes, the actual cohomology quotient and canonical Kummer maps.
-/

@[expose] public section

open GroupCohomology.ContinuousH1 GroupCohomology.Kummer
  Field.absoluteGaloisGroup.RootsOfUnity

section CocycleValues

variable {G A : Type*} [Group G] [TopologicalSpace G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A]

/-- Conjugation and power formulas compose on the same actual cocycle. -/
example (c : Cocycle G A) (g h : G) (hfixed : ∀ a : A, h • a = a) (n : ℕ) :
    c.val ((g * h * g⁻¹) ^ n) = n • (g • c.val h) := by
  have hconj : ∀ a : A, (g * h * g⁻¹) • a = a := by
    intro a
    rw [mul_smul, mul_smul, hfixed, smul_inv_smul]
  rw [c.power_value _ hconj, c.conjugation_value g h hfixed]

end CocycleValues

section PointedCharacters

open GroupCohomology.PointedCohomology
  GroupCohomology.PointedCohomology.CharacterFactorization

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]
  (m : ℕ) [NeZero m] [DistribMulAction G (ZMod m)] [ContinuousSMul G (ZMod m)]
  [DistribMulAction G (ZMod 1)] [ContinuousSMul G (ZMod 1)]

/-- Factoring the zero pointed class at its actual order gives the zero class
at level one, for an arbitrary possibly infinite noncommutative geometric group. -/
example
    (he : ∀ (g : G) (a : ZMod 1),
      ZMod.divisorInsertion (one_dvd m) (g • a) =
        g • ZMod.divisorInsertion (one_dvd m) a) :
    factorPointed (N := N) (one_dvd m) he 0 (by simp) = 0 := by
  exact (factorPointed_eq_zero_iff (one_dvd m) he 0 (by simp)).mpr rfl

end PointedCharacters

section QuotientDescent

variable {G H A : Type*} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [DistribMulAction H A]

/-- A descended representative has the original cocycle value on a product,
using the supplied quotient topology and coefficient action compatibility. -/
example (p : ContinuousMonoidHom G H) (hp : Topology.IsQuotientMap p)
    (ha : ∀ (g : G) (a : A), g • a = p g • a)
    (c : Cocycle G A) (hc : ∀ g : G, p g = 1 → c.val g = 0) :
    ∃ d : Cocycle H A, ∀ g h : G,
      d.val (p g * p h) = c.val g + g • c.val h := by
  obtain ⟨d, hd⟩ := Inflation.exists_descended_cocycle p hp ha c hc
  refine ⟨d, fun g h => ?_⟩
  rw [← map_mul, hd, c.map_mul]

end QuotientDescent

section InnerConjugacy

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- The combined inner-conjugacy map fixes an arbitrary actual H1 class. -/
example (g : G) (q : H1 G A) : (InnerConjugacy.conjugacyMap G A g).onH1 q = q := by
  rw [InnerConjugacy.conjugacyMap_onH1]
  rfl

end InnerConjugacy

/-- Over the rationals, surjectivity and the square-kernel theorem refer to
exactly the same continuous Kummer map and actual roots-of-unity coefficient. -/
example (q : H1 (Field.absoluteGaloisGroup ℚ) (Mu ℚ 2)) :
    ∃ u : ℚˣ, kummer ℚ 2 (by decide) u = q ∧
      (kummer ℚ 2 (by decide) u = 0 ↔ ∃ a : ℚˣ, a ^ 2 = u) := by
  obtain ⟨u, hu⟩ := kummer_surjective ℚ 2 (by decide) q
  exact ⟨u, hu, kummer_eq_zero_iff ℚ 2 (by decide) u⟩

/-- A base-field root remains fixed after applying the same action twice,
including level zero. -/
example (K : Type*) [Field K] (n : ℕ) (z : rootsOfUnity n K)
    (g h : Field.absoluteGaloisGroup K) :
    unitAction K (g * h) ((baseRoot K n z).toMul : (AlgebraicClosure K)ˣ) =
      ((baseRoot K n z).toMul : (AlgebraicClosure K)ˣ) := by
  rw [unitAction_mul, unitAction_baseRoot, unitAction_baseRoot]

section TameCharacters

open integralClosure.Inertia
open IsLocalRing

universe u v
variable (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]
  (Q : Ideal (IntegralModel R K)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)]
  (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

/-- Surjectivity is unchanged when the same actual tame character is presented
using a different irreducible uniformizer. -/
example {π τ : R} (hπ : Irreducible π) (hτ : Irreducible τ)
    (z : Multiplicative (Mu K n)) :
    ∃ g : inertia R K Q, tameCharacter R K Q n hn hnunit hτ g = z := by
  rw [tameCharacter_independent R K Q n hn hnunit hπ hτ]
  exact tameCharacter_surjective R K Q n hn hnunit hπ z

end TameCharacters
