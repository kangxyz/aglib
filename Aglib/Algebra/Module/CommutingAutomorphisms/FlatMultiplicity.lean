/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.RealizationBaseChange
public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Aglib.RingTheory.Localization.LengthFlatBaseChange
public import Aglib.RingTheory.Ideal.MinimalPrime.FlatBaseChange
public import Mathlib.RingTheory.Support

/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/FlatMultiplicity.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fb05d18e7d2d79d5ef5fcda82a810c674139fe71e11a251f8da919432fd5cbca`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct AlgebraMonoidAlgebra
namespace Module.CommutingAutomorphisms
open LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The length of the ORIGINAL localized module is positive precisely on its
annihilator support. Finiteness over the Laurent ring is derived from Object. -/
theorem ambientLength_ne_zero_iff (X : Object R)
    (p : Ideal (Laurent R)) [p.IsPrime] :
    ambientLength X p ≠ 0 ↔ supportIdeal X ≤ p := by
  let e := IsLocalizedModule.iso p.primeCompl
    (TensorProduct.mk (Laurent R) (Localization.AtPrime p) (Realization X) 1)
  have hs : Nontrivial (LocalRealization X p) ↔
      Nontrivial (LocalizedModule p.primeCompl (Realization X)) :=
    ⟨fun h => by let := h; exact e.nontrivial,
      fun h => by let := h; exact e.symm.nontrivial⟩
  change Module.length (Localization.AtPrime p) (LocalRealization X p) ≠ 0 ↔ _
  rw [ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial, hs]
  change (⟨p, inferInstance⟩ : PrimeSpectrum (Laurent R)) ∈
    Module.support (Laurent R) (Realization X) ↔ _
  rw [Module.mem_support_iff_of_finite, realization_annihilator]

/-- At a cycle label, a nonzero natural coefficient is equivalent to actual
support membership. This includes coincident components and the zero object. -/
theorem coefficient_ne_zero_iff [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R) :
    coefficient X p ≠ 0 ↔ supportIdeal X ≤ p.val := by
  rw [← ambientLength_ne_zero_iff X p.val, ← coefficient_coe X p]
  exact_mod_cast Iff.rfl

/-- Every actual minimal extended support prime contracts to an actual minimal
original support prime. Flatness alone suffices for this contraction statement. -/
theorem minimalSupport_baseChange_under [Module.Flat R S]
    (X : Object R) (q : Ideal (Laurent S))
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    q.under (Laurent R) ∈ (supportIdeal X).minimalPrimes := by
  let : Module.Flat (Laurent R) (Laurent S) := laurent_flat_baseChange
  rw [supportIdeal_baseChange] at hq
  exact _root_.Ideal.minimalPrime_map_under (supportIdeal X) q hq

/-- Exact partition of actual minimal support primes by their contracted
original components and the minimal primes of each literal extended component. -/
theorem minimalSupport_baseChange_iff [Module.Flat R S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime] :
    q ∈ (supportIdeal (X.baseChange S)).minimalPrimes ↔
      q.under (Laurent R) ∈ (supportIdeal X).minimalPrimes ∧
      q ∈ ((q.under (Laurent R)).map (coefficientMap (algebraMap R S))).minimalPrimes := by
  let : Module.Flat (Laurent R) (Laurent S) := laurent_flat_baseChange
  rw [supportIdeal_baseChange]
  exact _root_.Ideal.minimalPrime_map_iff (supportIdeal X) q

/-- The literal local residue-fibre length of the Laurent coefficient map.
This is not the degree of the residue-field extension. -/
def residueFibreLength (q : Ideal (Laurent S)) [q.IsPrime] : ℕ∞ :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under (Laurent R)) q
  Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under (Laurent R)))).map
        (algebraMap (Localization.AtPrime (q.under (Laurent R))) (Localization.AtPrime q)))

theorem residueFibreLength_ne_zero (q : Ideal (Laurent S)) [q.IsPrime] :
    residueFibreLength (R := R) q ≠ 0 := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under (Laurent R)) q
  simpa [residueFibreLength, ← pos_iff_ne_zero, Module.length_pos_iff] using
    (IsLocalRing.map_maximalIdeal_lt_top
      (algebraMap (Localization.AtPrime (q.under (Laurent R))) (Localization.AtPrime q))).ne

/-- Finiteness of the literal fibre factor on actual extended support is
proved from finite target length, positive source length and the accepted flat
local length formula; it is not a finite-multiplicity hypothesis. -/
theorem residueFibreLength_ne_top [Module.Flat R S] [IsNoetherianRing S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    residueFibreLength (R := R) q ≠ ⊤ := by
  have hp := minimalSupport_baseChange_under X q hq
  have hp0 := (ambientLength_ne_zero_iff X (q.under (Laurent R))).mpr hp.le
  have hlen : ambientLength (X.baseChange S) q =
      ambientLength X (q.under (Laurent R)) * residueFibreLength (R := R) q :=
    ambientLength_flat_baseChange X q
  intro ht
  apply ambientLength_ne_top (X.baseChange S) q hq
  rw [hlen, ht, ENat.mul_top hp0]

/-- Natural local fibre multiplicity; its meaningful finite interpretation on
actual support is guaranteed by residueFibreMultiplicity_coe below. -/
def residueFibreMultiplicity (q : Ideal (Laurent S)) [q.IsPrime] : ℕ :=
  (residueFibreLength (R := R) q).toNat

theorem residueFibreMultiplicity_coe [Module.Flat R S] [IsNoetherianRing S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    (residueFibreMultiplicity (R := R) q : ℕ∞) = residueFibreLength (R := R) q :=
  ENat.natCast_toNat (residueFibreLength_ne_top X q hq)

theorem residueFibreMultiplicity_pos [Module.Flat R S] [IsNoetherianRing S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    0 < residueFibreMultiplicity (R := R) q := by
  have h := residueFibreLength_ne_zero (R := R) q
  rw [← residueFibreMultiplicity_coe X q hq] at h
  exact_mod_cast (pos_iff_ne_zero.mpr h)

/-- The contracted ORIGINAL component as an actual finite dominant cycle
label. The input is an actual minimal extended support prime, not an arbitrary
target label. -/
def contractedSupportPoint [Module.Flat R S] [IsNoetherianRing R] [IsDomain R]
    (X : Object R) (q : Ideal (Laurent S))
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) : FiniteDominantPrime R :=
  minimalPoint X (q.under (Laurent R)) (minimalSupport_baseChange_under X q hq)

/-- Actual natural cycle coefficients multiply by the literal finite positive
residue-fibre length. Valid for arbitrary flat maps of Noetherian domains,
including arbitrary field extensions and their polynomial/simplex charts. -/
theorem coefficient_flat_baseChange [Module.Flat R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    (X : Object R) (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q ∈ (supportIdeal (X.baseChange S)).minimalPrimes) :
    coefficient (X.baseChange S) (minimalPoint (X.baseChange S) q hq) =
      coefficient X (contractedSupportPoint X q hq) *
        residueFibreMultiplicity (R := R) q := by
  let : q.IsPrime := hq.isPrime
  change (ambientLength (X.baseChange S) q).toNat =
    (ambientLength X (q.under (Laurent R))).toNat * (residueFibreLength (R := R) q).toNat
  have h := ambientLength_flat_baseChange X q
  exact (congrArg ENat.toNat h).trans (ENat.toNat_mul _ _)

/-- Consumer form at an existing target cycle label in the actual support. -/
theorem coefficient_flat_baseChange_at_point [Module.Flat R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    (X : Object R) (q : FiniteDominantPrime S) (hq : supportIdeal (X.baseChange S) ≤ q.val) :
    coefficient (X.baseChange S) q =
      coefficient X (contractedSupportPoint X q.val
        (minimal_of_support_le (X.baseChange S) q.val
          (MonoidAlgebra.FiniteDominantPrime.under_eq_bot q) hq)) *
        residueFibreMultiplicity (R := R) q.val :=
  coefficient_flat_baseChange X q.val
    (minimal_of_support_le (X.baseChange S) q.val
          (MonoidAlgebra.FiniteDominantPrime.under_eq_bot q) hq)

/-- Outside actual support the target coefficient vanishes, so no contracted
FiniteDominantPrime R is needed for an arbitrary target label. -/
theorem coefficient_baseChange_zero_off_support [IsNoetherianRing S]
    (X : Object R) (q : FiniteDominantPrime S) (hq : ¬ supportIdeal (X.baseChange S) ≤ q.val) :
    coefficient (X.baseChange S) q = 0 := by
  by_contra h
  exact hq ((coefficient_ne_zero_iff (X.baseChange S) q).mp h)

end Module.CommutingAutomorphisms
