/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.LocalLength
public import Aglib.RingTheory.MonoidAlgebra.FiniteDominantPrimes
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The finite dominant torus-prime labels of the actual cycle

Labels are ordinary prime ideals whose integral closed subschemes are finite
and dominant over the base. Nonzero coefficients are proved to occur among
the finitely many actual minimal support primes.
-/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/SupportPoints.lean`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d97baddff914894d7325740a5ea5068f1463bfb6172ce6442e7758eef5be3fec`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module.CommutingAutomorphisms
open LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
universe u
variable {R : Type u} [CommRing R]

/-- Outside the actual annihilator support, the ORIGINAL localized module is zero. -/
theorem ambientLength_zero_of_not_le (X : Object R) (p : Ideal (Laurent R)) [p.IsPrime]
    (hp : ¬ supportIdeal X ≤ p) : ambientLength X p = 0 := by
  obtain ⟨a, ha, hap⟩ := SetLike.not_le_iff_exists.mp hp
  have hann : a ∈ Module.annihilator (Laurent R) (Realization X) := by
    rwa [realization_annihilator]
  have hz := (Module.mem_annihilator.mp hann)
  have hsub : Subsingleton (LocalRealization X p) := by
    apply (IsLocalizedModule.subsingleton_iff p.primeCompl
      (TensorProduct.mk (Laurent R) (Localization.AtPrime p) (Realization X) 1)).mpr
    intro x
    exact ⟨a, hap, hz x⟩
  exact Module.length_eq_zero_iff.mpr hsub

/-- A dominant prime containing the actual support is a minimal support prime.
This uses finiteness/integrality of the actual support algebra. -/
theorem minimal_of_support_le [IsNoetherianRing R] (X : Object R)
    (p : Ideal (Laurent R)) [p.IsPrime] (hp : p.under R = ⊥)
    (hI : supportIdeal X ≤ p) : p ∈ (supportIdeal X).minimalPrimes := by
  let q : Ideal (Support X) := p.map (Ideal.Quotient.mk (supportIdeal X))
  let : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hI
  have hqA : q.under (Laurent R) = p := Ideal.comap_map_mk hI
  have hqR : q.under R = ⊥ := by
    rw [← Ideal.under_under (A := R) (B := Laurent R) q, hqA, hp]
  have hq : q ∈ minimalPrimes (Support X) := by
    have h := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) q
    simpa [hqR] using h
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨q, hq, hqA⟩

/-- The actual minimal support components form a finite set. -/
theorem finite_minimal_support [IsNoetherianRing R] (X : Object R) :
    (supportIdeal X).minimalPrimes.Finite := by
  let : IsNoetherianRing (Support X) := IsNoetherianRing.of_finite R (Support X)
  rw [Ideal.minimalPrimes_eq_comap]
  exact (minimalPrimes.finite_of_isNoetherianRing (Support X)).image _

/-- At every finite dominant label the ORIGINAL ambient local length is finite. -/
theorem pointLength_ne_top [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R) :
    ambientLength X p.val ≠ ⊤ := by
  by_cases hI : supportIdeal X ≤ p.val
  · exact ambientLength_ne_top X p.val
      (minimal_of_support_le X p.val (MonoidAlgebra.FiniteDominantPrime.under_eq_bot p) hI)
  · rw [ambientLength_zero_of_not_le X p.val hI]
    exact ENat.zero_ne_top

/-- The nonzero coefficients can occur only at ACTUAL minimal support components. -/
theorem pointLength_support [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R)
    (hp : ambientLength X p.val ≠ 0) : p.val ∈ (supportIdeal X).minimalPrimes := by
  apply minimal_of_support_le X p.val (MonoidAlgebra.FiniteDominantPrime.under_eq_bot p)
  by_contra hI
  exact hp (ambientLength_zero_of_not_le X p.val hI)

/-- The numerical coefficient is derived from the actual finite local length. -/
def coefficient (X : Object R) (p : FiniteDominantPrime R) : ℕ := (ambientLength X p.val).toNat

theorem coefficient_coe [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R) :
    (coefficient X p : ℕ∞) = ambientLength X p.val :=
  ENat.natCast_toNat (pointLength_ne_top X p)

theorem coefficient_iso {X Y : Object R} (e : Object.Iso X Y) (p : FiniteDominantPrime R) :
    coefficient X p = coefficient Y p := by
  simp only [coefficient, ambientLength_iso e]

theorem coefficient_sum [IsNoetherianRing R] (X Y : Object R) (p : FiniteDominantPrime R) :
    coefficient (X.sum Y) p = coefficient X p + coefficient Y p := by
  exact (congrArg ENat.toNat (ambientLength_sum X Y p.val)).trans
    (ENat.toNat_add (pointLength_ne_top X p) (pointLength_ne_top Y p))

/-- The actual coefficient function has finite support; this is not supplied as data. -/
theorem coefficient_finiteSupport [IsNoetherianRing R] (X : Object R) :
    (Function.support (coefficient X)).Finite := by
  apply Set.Finite.subset
    ((finite_minimal_support X).preimage (f := fun p : FiniteDominantPrime R => p.val)
      Subtype.val_injective.injOn)
  intro p hp
  apply pointLength_support X p
  intro hz
  apply hp
  simp [coefficient, hz]

/-- Over a domain EVERY actual minimal support prime supplies a cycle label. -/
def minimalPoint [IsNoetherianRing R] [IsDomain R] (X : Object R)
    (p : Ideal (Laurent R)) (hp : p ∈ (supportIdeal X).minimalPrimes) : FiniteDominantPrime R :=
  ⟨p, hp.isPrime, minimal_component_finite X p hp, minimalPrime_contract X p hp⟩

/-- Label of a minimal prime of the ACTUAL intrinsic support algebra. -/
def intrinsicPoint [IsNoetherianRing R] [IsDomain R] (X : Object R)
    (q : Ideal (Support X)) (hq : q ∈ minimalPrimes (Support X)) : FiniteDominantPrime R :=
  minimalPoint X (q.under (Laurent R)) (by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q, hq, rfl⟩)

/-- The coefficient at an actual support component is the accepted intrinsic
multiplicity, with no substituted module or scalar extension. -/
theorem coefficient_intrinsicPoint [IsNoetherianRing R] [IsDomain R] (X : Object R)
    (q : Ideal (Support X)) [q.IsPrime] (hq : q ∈ minimalPrimes (Support X)) :
    coefficient X (intrinsicPoint X q hq) = multiplicity X q := by
  change (ambientLength X (q.under (Laurent R))).toNat = (localLength X q).toNat
  rw [ambientLength_eq_intrinsic]

end Module.CommutingAutomorphisms
