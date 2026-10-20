/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalEuler
public import Aglib.RingTheory.Length.ExactSequence
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Aglib.RingTheory.ScalarHomology.Basic
public import Aglib.RingTheory.PrimeFiltration.Basic
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Filtration
public import Aglib.RingTheory.PrimeFiltration.Primes
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import Aglib.RingTheory.MonoidAlgebra.FiniteType

/-!
# Principal-face associativity on the original Laurent module

Supporting auxiliary for `K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The actual original localized Laurent realization is the module in the filtration, finite-homology
and weighted associativity constructions. The left-hand coefficient is identified by the maintained
principal-cokernel theorem.

This module supplies the stated local algebraic construction; it does not
claim a full original face-cycle or motivic comparison theorem.
-/
/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/PrincipalAssociativity.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7e9091f7e8cf006672b38933fa6dca344bcf66af042d34f631497f63fa329a62`.
-/

@[expose] public section

open _root_.Module
  (FinitePrincipal PrimeFiltrationFrom minimalPrimeCokernelTerm
    minimalPrimeEulerTerm_eq_cokernelTerm moduleMinimalPrimes nonempty_primeFiltration
    principalEuler_associativity supportDim_le_one_of_finite_cokernel)
open _root_.MonoidAlgebra (monoidAlgebra_isNoetherianRing)

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module.CommutingAutomorphisms
open LaurentSupport
open _root_.Module
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance laurent_isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing (Laurent R) :=
  monoidAlgebra_isNoetherianRing R Character

/-- An actual finite prime filtration of the same original localized Laurent
module used in the proved principal-face cokernel model. -/
def localOriginalPrimeFiltration [IsNoetherianRing R]
    (X : Object R) (Q : Ideal (Laurent R)) [Q.IsPrime] :
    PrimeFiltrationFrom (A := Localization.AtPrime Q) (LocalRealization X Q) ⊥ :=
  Classical.choice (nonempty_primeFiltration (A := Localization.AtPrime Q) (LocalRealization X Q))

theorem localOriginal_supportDim_le_one [IsNoetherianRing R] [IsNoetherianRing S]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    Module.supportDim (Localization.AtPrime (q.under (Laurent R)))
      (LocalRealization X (q.under (Laurent R))) ≤ 1 := by
  have htz : algebraMap R S t = 0 := by
    apply RingHom.mem_ker.mp
    rw [ht]
    exact Ideal.subset_span (Set.mem_singleton t)
  exact supportDim_le_one_of_finite_cokernel _
    (localOriginalScalar_mem_maximalIdeal t htz q)
    (localOriginal_finitePrincipal X t h ht hr q hq).2

/-- All submodules and actual prime factors have finite principal homology,
derived on the original local object from its already proved finite cokernel. -/
theorem localOriginalPrimeFiltration_finitePrincipal [IsNoetherianRing R] [IsNoetherianRing S]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    letI : AddCommGroup (LocalRealization X (q.under (Laurent R))) := inferInstance
    (∀ V : Submodule (Localization.AtPrime (q.under (Laurent R)))
      (LocalRealization X (q.under (Laurent R))),
      FinitePrincipal (A := Localization.AtPrime (q.under (Laurent R))) V
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t)) ∧
    (∀ p ∈ (localOriginalPrimeFiltration X (q.under (Laurent R))).primes,
      FinitePrincipal (Localization.AtPrime (q.under (Laurent R)) ⧸ p)
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t)) :=
  (localOriginalPrimeFiltration X (q.under (Laurent R))).finitePrincipal_terms _
    (localOriginal_finitePrincipal X t h ht hr q hq).2

/-- The weights are lengths of the literal original M_Q localized again at
its minimal support primes. They are proved equal to occurrence counts. -/
theorem localOriginalPrimeFiltration_multiplicity [IsNoetherianRing R]
    (X : Object R) (Q : Ideal (Laurent R)) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime]
    (hp : p ∈ (Module.annihilator (Localization.AtPrime Q) (LocalRealization X Q)).minimalPrimes) :
    letI : AddCommGroup (Localization.AtPrime p) := inferInstance
    letI : AddCommGroup (LocalRealization X Q) := inferInstance
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[Localization.AtPrime Q] LocalRealization X Q) =
        ((localOriginalPrimeFiltration X Q).primes.count p : ℕ∞) :=
  (localOriginalPrimeFiltration X Q).localized_length_eq_count_of_bot p hp

/-- Weighted principal Euler associativity on the literal original local
Laurent realization. The coefficient on the left is the actual target
base-change coefficient from the maintained principal-cokernel theorem. -/
theorem principalFace_local_weighted_associativity [IsNoetherianRing R] [IsNoetherianRing S]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t)
    (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    ((ambientLength (X.baseChange S) q).toNat : ℤ) =
      ∑ p ∈ moduleMinimalPrimes (A := Localization.AtPrime (q.under (Laurent R)))
        (LocalRealization X (q.under (Laurent R))),
      minimalPrimeCokernelTerm (LocalRealization X (q.under (Laurent R)))
        (algebraMap R (Localization.AtPrime (q.under (Laurent R))) t) p := by
  have htz : algebraMap R S t = 0 := by
    apply RingHom.mem_ker.mp
    rw [ht]
    exact Ideal.subset_span (Set.mem_singleton t)
  rw [← principalEuler_local_original_baseChange X t h ht hr q,
    principalEuler_associativity _ (localOriginalScalar_mem_maximalIdeal t htz q)
      (localOriginal_finitePrincipal X t h ht hr q hq).2]
  exact Finset.sum_congr rfl fun p _ => minimalPrimeEulerTerm_eq_cokernelTerm _
    (localOriginalScalar_regular X t hr (q.under (Laurent R))) p

end Module.CommutingAutomorphisms
