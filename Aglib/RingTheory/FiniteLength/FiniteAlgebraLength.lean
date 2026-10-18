/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Mathlib.Algebra.BigOperators.WithTop

/-!
# Finite-algebra lengths across all closed fiber points

The literal prime filtration computes restricted length. For a finite-length
module its factors are maximal quotients, and localization at every maximal
point counts exactly those factors. Grouping the factors proves the weighted
length formula, including multiple points over the same closed base point.
No decomposition of the algebra into Artinian local rings is assumed.

Aglib migration adaptation: downstream filtration methods use explicit
qualified calls because the filtration now has its native Module owner.
Statements and hypotheses are unchanged.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The actual filtration exact sequences remain exact on restriction of scalars. -/
theorem length_restrictScalars_add_of_submodule_le
    (U V : Submodule S M) (hUV : U ≤ V) :
    Module.length R V = Module.length R U + Module.length R (V ⧸ U.comap V.subtype) := by
  let C : Submodule S V := U.comap V.subtype
  let f : U →ₗ[S] V := Submodule.inclusion hUV
  have hex : Function.Exact f C.mkQ := by
    apply LinearMap.exact_iff.mpr
    simp only [f, C, Submodule.range_inclusion, Submodule.ker_mkQ]
  exact Module.length_eq_add_of_exact (f.restrictScalars R) (C.mkQ.restrictScalars R)
    (Submodule.inclusion_injective hUV) (Submodule.mkQ_surjective C) hex

namespace PrimeFiltrationFrom

/-- Restricted length is computed from the actual successive prime quotients. -/
theorem length_restrictScalars_eq_add_sum
    {U : Submodule S M} (D : Module.PrimeFiltrationFrom M U) :
    Module.length R M = Module.length R U +
      (D.primes.map fun p => Module.length R (S ⧸ p)).sum := by
  induction D with
  | top =>
    simpa only [Module.PrimeFiltrationFrom.primes, List.map_nil, List.sum_nil, add_zero] using
      ((Submodule.topEquiv (R := S) (M := M)).restrictScalars R).length_eq.symm
  | @step U V hUV p hp e tail ih =>
    have hstep := length_restrictScalars_add_of_submodule_le (R := R) U V hUV.le
    rw [(e.restrictScalars R).length_eq] at hstep
    rw [hstep] at ih
    simpa only [Module.PrimeFiltrationFrom.primes, List.map_cons, List.sum_cons, add_assoc] using ih

/-- Every factor of a finite-length module's actual prime filtration is maximal. -/
theorem primes_isMaximal_of_length_ne_top {U : Submodule S M}
    (D : Module.PrimeFiltrationFrom M U) (hM : Module.length S M ≠ ⊤)
    (p : Ideal S) (hp : p ∈ D.primes) : p.IsMaximal :=
  Module.isMaximal_of_mem_support_of_length_ne_top hM
    ⟨p, D.primes_isPrime p hp⟩ (D.prime_mem_support p hp)

/-- At any maximal point, including points outside the support, localized
length equals the number of its factors in the actual complete filtration. -/
theorem localized_length_eq_count_of_finiteLength (D : Module.PrimeFiltrationFrom M ⊥)
    (hM : Module.length S M ≠ ⊤) (p : MaximalSpectrum S) :
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[S] M) = (D.primes.count p.asIdeal : ℕ∞) := by
  classical
  rw [D.length_baseChange_eq_add_sum (Localization.AtPrime p.asIdeal),
    Module.length_eq_zero, zero_add]
  have hfac : ∀ q ∈ D.primes,
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[S] (S ⧸ q)) =
          if q = p.asIdeal then 1 else 0 := by
    intro q hq
    exact Module.localized_primeQuotient_length p.asIdeal q fun hqp =>
      (Module.PrimeFiltrationFrom.primes_isMaximal_of_length_ne_top D hM q hq).eq_of_le
        p.isMaximal.ne_top hqp
  have aux : ∀ ps : List (Ideal S),
      (∀ q ∈ ps,
        Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[S] (S ⧸ q)) =
            if q = p.asIdeal then 1 else 0) →
      (ps.map fun q => Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[S] (S ⧸ q))).sum =
          (ps.count p.asIdeal : ℕ∞) := by
    intro ps
    induction ps with
    | nil => intro _; simp
    | cons q ps ih =>
      intro hh
      have hq := hh q (by simp)
      have hs := ih (fun r hr => hh r (List.mem_cons_of_mem q hr))
      by_cases hqp : q = p.asIdeal
      · subst q
        simp [hq, hs, add_comm]
      · simp [hq, hs, hqp]
  exact aux D.primes hfac

end PrimeFiltrationFrom

variable (R S) [IsLocalRing R] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

/-- Group the literal maximal quotient factors by every point of the finite
closed fiber. Repeated occurrences contribute their multiplicities. -/
theorem sum_maximalQuotient_lengths [Fintype (MaximalSpectrum S)]
    (ps : List (Ideal S)) (hps : ∀ p ∈ ps, p.IsMaximal) :
    (ps.map fun p => Module.length R (S ⧸ p)).sum =
      ∑ p : MaximalSpectrum S,
        (ps.count p.asIdeal : ℕ∞) * (finiteAlgebraResidueDegree R S p : ℕ∞) := by
  classical
  induction ps with
  | nil => simp
  | cons q ps ih =>
    have hq := hps q (by simp)
    have hs := ih (fun p hp => hps p (List.mem_cons_of_mem q hp))
    let q' : MaximalSpectrum S := ⟨q, hq⟩
    have hdelta :
        (∑ p : MaximalSpectrum S, (if q = p.asIdeal then (1 : ℕ∞) else 0) *
          (finiteAlgebraResidueDegree R S p : ℕ∞)) = Module.length R (S ⧸ q) := by
      rw [Finset.sum_eq_single q']
      · simpa only [q', ite_true, one_mul] using
          (finiteAlgebra_residue_length R S q').symm
      · intro p _ hp
        have hne : q ≠ p.asIdeal := fun h => hp (MaximalSpectrum.ext h.symm)
        simp [hne]
      · simp
    simp only [List.map_cons, List.sum_cons, List.count_cons, beq_iff_eq,
      Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
      Finset.sum_add_distrib]
    rw [← hs, hdelta, add_comm]

/-- Stacks 02M0 for a finite algebra over a Noetherian local ring, with the
literal localized modules and every maximal point of the closed fiber. -/
theorem finiteAlgebra_length_eq_sum [IsNoetherianRing R]
    [Fintype (MaximalSpectrum S)] (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ p : MaximalSpectrum S,
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[S] M) *
          (finiteAlgebraResidueDegree R S p : ℕ∞) := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : IsNoetherian S M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hM)).1
  obtain ⟨D⟩ := Module.nonempty_primeFiltrationFrom (A := S) M ⊥
  rw [Module.PrimeFiltrationFrom.length_restrictScalars_eq_add_sum D (R := R),
    Module.length_eq_zero, zero_add]
  rw [sum_maximalQuotient_lengths R S D.primes
    (Module.PrimeFiltrationFrom.primes_isMaximal_of_length_ne_top D hM)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Module.PrimeFiltrationFrom.localized_length_eq_count_of_finiteLength D hM p]

/-- The canonical sum over every maximal point, using finiteness proved from
the finite algebra rather than a supplied enumeration hypothesis. -/
def finiteAlgebraFiberLengthSum : ℕ∞ :=
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  ∑ p : MaximalSpectrum S,
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[S] M) *
        (finiteAlgebraResidueDegree R S p : ℕ∞)

/-- The all-point fiber formula with no independently supplied semilocality,
residue-finiteness or point-enumeration hypothesis. -/
theorem finiteAlgebra_length_eq_fiberSum [IsNoetherianRing R]
    (hM : Module.length S M ≠ ⊤) :
    Module.length R M = finiteAlgebraFiberLengthSum (M := M) R S := by
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  exact finiteAlgebra_length_eq_sum R S hM

/-- Restriction along a finite algebra preserves genuine finite module length. -/
theorem finiteAlgebra_length_ne_top [IsNoetherianRing R]
    (hM : Module.length S M ≠ ⊤) : Module.length R M ≠ ⊤ := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : IsNoetherian S M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hM)).1
  obtain ⟨D⟩ := Module.nonempty_primeFiltrationFrom (A := S) M ⊥
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  rw [finiteAlgebra_length_eq_sum R S hM]
  apply WithTop.sum_ne_top.mpr
  intro p _
  rw [Module.PrimeFiltrationFrom.localized_length_eq_count_of_finiteLength D hM p]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (ENat.natCast_ne_top _)

end Module
