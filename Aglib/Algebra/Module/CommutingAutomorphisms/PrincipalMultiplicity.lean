/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Localization.PrincipalQuotientLength
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalAssociativity
public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Localization.IteratedModuleLength
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
public import Aglib.RingTheory.Support.Localization

/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalCycleAssociativity.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`968599bdeb8cadcdad2e725bc667f1cc96a60f90c4003d953c98c144e25d4950`.
-/

@[expose] public section

open _root_.Module
  (ScalarCokernel iterated_localized_length localized_minimalSupport_iff mem_moduleMinimalPrimes
    minimalPrimeCokernelTerm minimalPrimeEulerTerm_eq_cokernelTerm moduleMinimalPrimes
    principalEuler_associativity)

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module.CommutingAutomorphisms
open LaurentSupport
open _root_.Module
open MonoidAlgebra (FiniteDominantPrime)
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

open Classical in
/-- Original minimal support primes retained below the actual target contraction. -/
def originalMinimalSupportBelow [IsNoetherianRing R]
    (X : Object R) (Q : Ideal (Laurent R)) : Finset (Ideal (Laurent R)) :=
  (finite_minimal_support X).toFinset.filter (fun P => P ≤ Q)

@[simp] theorem mem_originalMinimalSupportBelow [IsNoetherianRing R]
    (X : Object R) (Q P : Ideal (Laurent R)) :
    P ∈ originalMinimalSupportBelow X Q ↔ P ∈ (supportIdeal X).minimalPrimes ∧ P ≤ Q := by
  simp [originalMinimalSupportBelow]

open Classical in
/-- The two factors are original object length and actual specialized prime-quotient length. -/
def originalPrincipalFaceTerm (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime]
    (P : Ideal (Laurent R)) : ℤ :=
  if hp : P ∈ (supportIdeal X).minimalPrimes then
    letI := hp.isPrime
    ((ambientLength X P).toNat : ℤ) *
      ((Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[Laurent S]
          (Laurent S ⧸ P.map (coefficientMap (algebraMap R S))))).toNat : ℤ)
  else 0

theorem localOriginal_minimalSupport_iff (X : Object R)
    (Q : Ideal (Laurent R)) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    p ∈ (Module.annihilator (Localization.AtPrime Q) (LocalRealization X Q)).minimalPrimes ↔
      p.under (Laurent R) ∈ (supportIdeal X).minimalPrimes := by
  simpa only [realization_annihilator] using
    localized_minimalSupport_iff (M := Realization X) Q p

/-- The multiplicity is the length of the original object at the original prime. -/
theorem localOriginal_iterated_length (X : Object R)
    (Q : Ideal (Laurent R)) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    letI : AddCommGroup (Localization.AtPrime p) := inferInstance
    letI : AddCommGroup (LocalRealization X Q) := inferInstance
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[Localization.AtPrime Q] LocalRealization X Q) =
        ambientLength X (p.under (Laurent R)) :=
  iterated_localized_length (M := Realization X) Q p

theorem localOriginal_minimalTerm_transport (X : Object R) (t : R)
    (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R))
    (q : Ideal (Laurent S)) [q.IsPrime]
    (p : Ideal (Localization.AtPrime (q.under (Laurent R))))
    (hp : p ∈ (Module.annihilator (Localization.AtPrime (q.under (Laurent R)))
      (LocalRealization X (q.under (Laurent R)))).minimalPrimes) :
    minimalPrimeCokernelTerm (LocalRealization X (q.under (Laurent R)))
      (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t) p =
      originalPrincipalFaceTerm (S := S) X q (p.under (Laurent R)) := by
  let := hp.isPrime
  have hP := (localOriginal_minimalSupport_iff X (q.under (Laurent R)) p).mp hp
  have hf := localized_principalPrimeCokernel_length (p.under (Laurent R))
    (algebraMap R (Laurent R) t) (laurentCoefficient_surjective h)
      (laurentCoefficient_ker_principal t ht) q
  rw [IsLocalization.map_under (q.under (Laurent R)).primeCompl
    (Localization.AtPrime (q.under (Laurent R))) p] at hf
  rw [← IsScalarTower.algebraMap_apply R (Laurent R)
    (Localization.AtPrime (q.under (Laurent R))) t] at hf
  simp only [minimalPrimeCokernelTerm, dite_eq_left hp, originalPrincipalFaceTerm, dite_eq_left hP]
  rw [localOriginal_iterated_length X (q.under (Laurent R)) p]
  congr 2
  exact congrArg ENat.toNat hf

/-- Transport the actual local weighted sum to original Laurent primes. -/
theorem localOriginal_minimalSum_transport [IsNoetherianRing R]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R))
    (q : Ideal (Laurent S)) [q.IsPrime] :
    (∑ p ∈ moduleMinimalPrimes (A := Localization.AtPrime (q.under (Laurent R)))
      (LocalRealization X (q.under (Laurent R))),
      minimalPrimeCokernelTerm (LocalRealization X (q.under (Laurent R)))
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t) p) =
      ∑ P ∈ originalMinimalSupportBelow X (q.under (Laurent R)),
        originalPrincipalFaceTerm (S := S) X q P := by
  classical
  apply Finset.sum_bij (fun p _ => p.under (Laurent R))
  · intro p hp
    have hm := (mem_moduleMinimalPrimes p).mp hp
    let := hm.isPrime
    refine (mem_originalMinimalSupportBelow X _ _).mpr ⟨?_, ?_⟩
    · exact (localOriginal_minimalSupport_iff X _ p).mp hm
    · exact ((IsLocalization.AtPrime.orderIsoOfPrime
        (Localization.AtPrime (q.under (Laurent R))) (q.under (Laurent R)))
          ⟨p, hm.isPrime⟩).property.2
  · intro p₁ hp₁ p₂ hp₂ he
    have h₁ := congrArg (Ideal.map (algebraMap (Laurent R)
      (Localization.AtPrime (q.under (Laurent R))))) he
    rw [IsLocalization.map_under (q.under (Laurent R)).primeCompl
      (Localization.AtPrime (q.under (Laurent R))) p₁,
      IsLocalization.map_under (q.under (Laurent R)).primeCompl
      (Localization.AtPrime (q.under (Laurent R))) p₂] at h₁
    exact h₁
  · intro P hP
    rcases (mem_originalMinimalSupportBelow X _ _).mp hP with ⟨hm, hle⟩
    let := hm.isPrime
    let p := P.map (algebraMap (Laurent R) (Localization.AtPrime (q.under (Laurent R))))
    let : p.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime (q.under (Laurent R)) hle
    have hp : p ∈ moduleMinimalPrimes (A := Localization.AtPrime (q.under (Laurent R)))
        (LocalRealization X (q.under (Laurent R))) := by
      apply (mem_moduleMinimalPrimes p).mpr
      apply (localOriginal_minimalSupport_iff X _ p).mpr
      rwa [Ideal.under_map_of_isLocalizationAtPrime (q.under (Laurent R)) hle]
    exact ⟨p, hp, Ideal.under_map_of_isLocalizationAtPrime (q.under (Laurent R)) hle⟩
  · intro p hp
    have hm : p ∈ (Module.annihilator (Localization.AtPrime (q.under (Laurent R)))
        (LocalRealization X (q.under (Laurent R)))).minimalPrimes :=
      (mem_moduleMinimalPrimes (A := Localization.AtPrime (q.under (Laurent R)))
        (M := LocalRealization X (q.under (Laurent R))) p).mp hp
    exact localOriginal_minimalTerm_transport X t h ht q p hm

/-- Weighted principal associativity needs only finite actual target local length. -/
theorem principalFace_local_associativity_of_length_ne_top [IsNoetherianRing R]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hlen : ambientLength (X.baseChange S) q ≠ ⊤) :
    ((ambientLength (X.baseChange S) q).toNat : ℤ) =
      ∑ p ∈ moduleMinimalPrimes (A := Localization.AtPrime (q.under (Laurent R)))
        (LocalRealization X (q.under (Laurent R))),
      minimalPrimeCokernelTerm (LocalRealization X (q.under (Laurent R)))
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t) p := by
  have htz : algebraMap R S t = 0 := by
    apply RingHom.mem_ker.mp
    rw [ht]
    exact Ideal.subset_span (Set.mem_singleton t)
  have hM : Module.length (Localization.AtPrime (q.under (Laurent R)))
      (ScalarCokernel (LocalRealization X (q.under (Laurent R)))
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t)) ≠ ⊤ := by
    rw [← (localPrincipalCokernelScalarEquiv X t (q.under (Laurent R))).length_eq,
      ← ambientLength_principal_baseChange X t h ht q]
    exact hlen
  rw [← principalEuler_local_original_baseChange X t h ht hr q,
    principalEuler_associativity _ (localOriginalScalar_mem_maximalIdeal t htz q) hM]
  exact Finset.sum_congr rfl fun p _ => minimalPrimeEulerTerm_eq_cokernelTerm _
    (localOriginalScalar_regular X t hr (q.under (Laurent R))) p

/-- Weighted principal associativity indexed by the original Laurent support primes. -/
theorem principalFace_original_associativity_of_length_ne_top [IsNoetherianRing R]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hlen : ambientLength (X.baseChange S) q ≠ ⊤) :
    ((ambientLength (X.baseChange S) q).toNat : ℤ) =
      ∑ P ∈ originalMinimalSupportBelow X (q.under (Laurent R)),
        originalPrincipalFaceTerm (S := S) X q P :=
  (principalFace_local_associativity_of_length_ne_top X t h ht hr q hlen).trans
    (localOriginal_minimalSum_transport X t h ht q)

/-- Every actual finite dominant target label supplies the needed finiteness. -/
theorem principalFace_original_point_coefficient
    [IsNoetherianRing R] [IsNoetherianRing S]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : FiniteDominantPrime S) :
    (coefficient (X.baseChange S) q : ℤ) =
      ∑ P ∈ originalMinimalSupportBelow X (q.val.under (Laurent R)),
        originalPrincipalFaceTerm (S := S) X q.val P :=
  principalFace_original_associativity_of_length_ne_top X t h ht hr q.val
    (pointLength_ne_top (X.baseChange S) q)

end Module.CommutingAutomorphisms
