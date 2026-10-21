/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Localization.PrincipalQuotientLength
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.DominantFibres
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalRegularity
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalSpecialization

/-!
# PrincipalDominance for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `PrincipalDominance.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ef136495758344c1ba27f17e3388cc899964b262ee36382dc977a72318ac6409`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

open _root_.Module (scalar_regular_primeQuotient)



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport Module
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Dominance of the actual source label makes each nonzero base scalar
regular on its literal prime quotient. -/
theorem pointQuotient_laurentScalar_regular (p : FiniteDominantPrime R) (a : R) (ha : a ≠ 0) :
    IsSMulRegular (Laurent R ⧸ p.val) (algebraMap R (Laurent R) a) := by
  apply scalar_regular_primeQuotient
  intro hin
  have hmem : a ∈ p.val.under R := hin
  rw [MonoidAlgebra.FiniteDominantPrime.under_eq_bot p, Ideal.mem_bot] at hmem
  exact ha hmem

/-- Every minimal component of the actual principal specialization of a
finite dominant source point is dominant on the face, over a normal source base.
No point-flatness hypothesis is used. -/
theorem principalPoint_minimal_contract_zero [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (p : FiniteDominantPrime R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R))
    (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) :
    q.under S = ⊥ := by
  let := hq.isPrime
  let Q := q.under (Laurent R)
  let C := Laurent R ⧸ p.val
  let J := RingHom.ker (algebraMap R S)
  let : J.IsPrime := RingHom.ker_isPrime (algebraMap R S)
  have hL : Function.Surjective (coefficientMap (algebraMap R S)) :=
    laurentCoefficient_surjective h
  have hQ : Q ∈ (p.val ⊔ Ideal.span ({algebraMap R (Laurent R) t} : Set (Laurent
    R))).minimalPrimes := by
    have hh := Ideal.minimalPrimes_comap_of_surjective hL hq
    rw [Ideal.comap_map_of_surjective _ hL, ← RingHom.ker_eq_comap_bot,
      laurentCoefficient_ker_principal t ht] at hh
    exact hh
  have hP : p.val ≤ Q := hQ.le.trans' le_sup_left
  have hQC : Q.map (Ideal.Quotient.mk p.val) ∈
      ((Ideal.span ({algebraMap R (Laurent R) t} : Set (Laurent R))).map
        (Ideal.Quotient.mk p.val)).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
    refine ⟨Q, ?_, rfl⟩
    have hker : RingHom.ker (Ideal.Quotient.mk p.val) = p.val := by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem
    simpa only [hker, sup_comm] using hQ
  have hJ : J.map (algebraMap R C) =
      (Ideal.span ({algebraMap R (Laurent R) t} : Set (Laurent R))).map
        (Ideal.Quotient.mk p.val) := by
    change (RingHom.ker (algebraMap R S)).map (algebraMap R C) = _
    rw [ht]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hC := MonoidAlgebra.FiniteDominantPrime.minimalPrime_under_eq p J
    (Q.map (Ideal.Quotient.mk p.val)) (hJ.symm ▸ hQC)
  have hCQ : (Q.map (Ideal.Quotient.mk p.val)).under (Laurent R) = Q :=
    Ideal.comap_map_mk hP
  have hQR : Q.under R = J := by
    rw [← hCQ, Ideal.under_under]
    exact hC
  apply Ideal.comap_injective_of_surjective (algebraMap R S) h
  calc
    (q.under S).under R = q.under R := Ideal.under_under q
    _ = Q.under R := (Ideal.under_under (A := R) (B := Laurent R) q).symm
    _ = J := hQR
    _ = (⊥ : Ideal S).under R := rfl

/-- All minimal components of a proper principal face are actual maintained cycle labels. -/
def principalPointMinimalLabel [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (p : FiniteDominantPrime R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R))
    (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) : FiniteDominantPrime
      S := by
  let := quotientBaseChange_finite (S := S) p.val
  let : Module.Finite S (Laurent S ⧸ q) := Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ S hq.le).toLinearMap (Ideal.Quotient.factor_surjective hq.le)
  exact ⟨q, hq.isPrime, inferInstance, principalPoint_minimal_contract_zero p t h ht q hq⟩

end AlgebraicGeometry.Torus.FiniteCorrespondence
