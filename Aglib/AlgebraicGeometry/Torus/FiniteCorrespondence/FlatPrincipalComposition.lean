/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatPullback
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatDictionary
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalInterchange
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalComposition
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
public import Aglib.RingTheory.Localization.IteratedModuleLength
public import Aglib.RingTheory.Support.Localization
public import Aglib.RingTheory.Localization.LengthFlatBaseChange
public import Aglib.RingTheory.Ideal.MinimalPrime.FlatBaseChange

/-!
# FlatPrincipalComposition for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FlatPrincipalComposition.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b1a71ab38972a32c5e43eb22667755a3e627c0ffd98e17fb3fdba6fb6cd5b72b`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

open _root_.Ideal (minimalPrime_map_under)
open _root_.Module
  (ScalarCokernel localized_length_flat_baseChange localized_minimalSupport_iff
    mem_moduleMinimalPrimes minimalPrimeCokernelTerm moduleMinimalPrimes
    principalCokernel_associativity)


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct AlgebraMonoidAlgebra

namespace AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport Module
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T]

local instance laurentSelf_finite : Module.Finite (Laurent S) (Laurent S) := Module.Finite.self _

/-- The extended local length at `q` after both successive coefficient extensions of `p`. -/
abbrev doubleFibreLength (p : FiniteDominantPrime R) (q : FiniteDominantPrime T) : ℕ∞ :=
  Module.length (Localization.AtPrime q.val)
    (Localization.AtPrime q.val ⊗[Laurent T]
      (Laurent T ⧸ (p.val.map (coefficientMap (algebraMap R S))).map
        (coefficientMap (algebraMap S T))))

/-- The local weighted principal sum represents the literal cycle composition
whenever every first-fibre minimal component is dominant. This closure is
proved for the actual flat field extensions, rather than imposed on the map. -/
theorem minimalSum_eq_composition_of_dominant
    [IsNoetherianRing S] [IsNoetherianRing T]
    (p : FiniteDominantPrime R)
    (hdom : ∀ Q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes,
      Q.under S = ⊥)
    (b : S) (h₂ : Function.Surjective (algebraMap S T))
    (hb : RingHom.ker (algebraMap S T) = Ideal.span ({b} : Set S)) (q : FiniteDominantPrime T) :
    (∑ r ∈ moduleMinimalPrimes (A := Localization.AtPrime (q.val.under (Laurent S)))
      (LocalPointFibre (S := S) p (q.val.under (Laurent S))),
      minimalPrimeCokernelTerm (LocalPointFibre (S := S) p (q.val.under (Laurent S)))
        (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b) r) =
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T)
      (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p))) := by
  classical
  let I := p.val.map (coefficientMap (algebraMap R S))
  let Q := q.val.under (Laurent S)
  let B := Localization.AtPrime Q
  let N := LocalPointFibre (S := S) p Q
  let c := quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p)
  let s := c.support.filter (fun z => z.val ≤ Q)
  let label := fun (r : Ideal B) (hr : r ∈ moduleMinimalPrimes (A := B) N) =>
    let hm := (mem_moduleMinimalPrimes r).mp hr
    let := hm.isPrime
    let hmin := localPointFibre_minimal_under p Q r hm
    (⟨r.under (Laurent S), inferInstance, minimalFibre_finite p _ hmin,
      hdom _ hmin⟩ : FiniteDominantPrime S)
  have hsum : (∑ r ∈ moduleMinimalPrimes (A := B) N,
      minimalPrimeCokernelTerm N (algebraMap S B b) r) =
      ∑ z ∈ s, (quotientFibreMultiplicity (S := S) p z : ℤ) *
        (quotientFibreMultiplicity (S := T) z q : ℤ) := by
    apply Finset.sum_bij label
    · intro r hr
      have hm := (mem_moduleMinimalPrimes r).mp hr
      let := hm.isPrime
      apply Finset.mem_filter.mpr
      constructor
      · apply (quotientFibreCycleMap_of_support p (label r hr)).mpr
        exact (localPointFibre_minimal_under p Q r hm).le
      · exact ((IsLocalization.AtPrime.orderIsoOfPrime B Q) ⟨r, hm.isPrime⟩).property.2
    · intro r₁ h₁ r₂ h₂ he
      have hv := congrArg (fun z : FiniteDominantPrime S => z.val) he
      have hm₁ := (mem_moduleMinimalPrimes r₁).mp h₁
      have hm₂ := (mem_moduleMinimalPrimes r₂).mp h₂
      let := hm₁.isPrime
      let := hm₂.isPrime
      have hh := congrArg (Ideal.map (algebraMap (Laurent S) B)) hv
      exact (IsLocalization.map_under Q.primeCompl B r₁).symm.trans
        (hh.trans (IsLocalization.map_under Q.primeCompl B r₂))
    · intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hs, hle⟩
      let := quotientBaseChange_finite (S := S) p.val
      have hmin : z.val ∈ I.minimalPrimes :=
        minimal_of_finite_quotient_le I z.val
          (MonoidAlgebra.FiniteDominantPrime.under_eq_bot z)
          ((quotientFibreCycleMap_of_support p z).mp hs)
      let r := z.val.map (algebraMap (Laurent S) B)
      let : r.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime Q hle
      have hr : r ∈ moduleMinimalPrimes (A := B) N := by
        apply (mem_moduleMinimalPrimes r).mpr
        apply (localized_minimalSupport_iff (M := Laurent S ⧸ I) Q r).mpr
        rw [Ideal.annihilator_quotient, Ideal.under_map_of_isLocalizationAtPrime Q hle]
        exact hmin
      refine ⟨r, hr, ?_⟩
      apply Subtype.ext
      exact Ideal.under_map_of_isLocalizationAtPrime Q hle
    · intro r hr
      have hm : r ∈ (Module.annihilator B N).minimalPrimes :=
        (mem_moduleMinimalPrimes (A := B) (M := N) r).mp hr
      have hv : (label r hr).val = r.under (Laurent S) := rfl
      exact localPointFibre_minimalTerm_transport (R := R) (S := S) (T := T)
        p b h₂ hb q r hm (label r hr) hv
  have hdrop : (∑ z ∈ s, (quotientFibreMultiplicity (S := S) p z : ℤ) *
      (quotientFibreMultiplicity (S := T) z q : ℤ)) =
      ∑ z ∈ c.support, (quotientFibreMultiplicity (S := S) p z : ℤ) *
        (quotientFibreMultiplicity (S := T) z q : ℤ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hn
    have hnot : ¬ z.val ≤ Q := fun hh => hn (Finset.mem_filter.mpr ⟨hz, hh⟩)
    have hzero : quotientFibreMultiplicity (S := T) z q = 0 := by
      by_contra hne
      apply hnot
      exact Ideal.map_le_iff_le_comap.mp
        ((quotientFibreMultiplicity_ne_zero_iff z q).mp hne)
    simp only [hzero, Nat.cast_zero, mul_zero]
  rw [quotientFibreCycleMap_coeff]
  simp only [quotientFibreCycleMap_of_coeff]
  exact hsum.trans hdrop

theorem localPointFibre_scalar_regular_flat
    [IsDomain R] [IsDomain S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (b : S) (hb : b ≠ 0) (Q : Ideal (Laurent S)) [Q.IsPrime] :
    IsSMulRegular (LocalPointFibre (S := S) p Q) (algebraMap S (Localization.AtPrime Q) b) := by
  let C := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))
  let : Module.IsTorsionFree S C := pointQuotient_baseChange_torsionFree p
  have hr : IsSMulRegular C (algebraMap S (Laurent S) b) := by
    intro x y hxy
    apply (IsRegular.of_ne_zero hb).isSMulRegular (M := C)
    simpa only [algebraMap_smul] using hxy
  have hloc := hr.lTensor (Localization.AtPrime Q)
  intro x y hxy
  apply hloc
  simpa only [IsScalarTower.algebraMap_apply S (Laurent S) (Localization.AtPrime Q),
    algebraMap_smul] using hxy

/-- A flat extension followed by a regular principal face gives the actual
iterated fibre length. Unlike the double-principal theorem the first map is
not required surjective, and regularity is proved on its actual fibre module. -/
theorem flat_then_principal_coeff
    [IsDomain R] [IsDomain S] [Module.Flat R S]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (p : FiniteDominantPrime R) (b : S) (hb0 : b ≠ 0)
    (h₂ : Function.Surjective (algebraMap S T))
    (hb : RingHom.ker (algebraMap S T) = Ideal.span ({b} : Set S)) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T)
      (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p))) =
        ((doubleFibreLength (S := S) p q).toNat : ℤ) := by
  have hbz : algebraMap S T b = 0 := by
    apply RingHom.mem_ker.mp
    rw [hb]
    exact Ideal.subset_span (Set.mem_singleton b)
  have hlen : Module.length (Localization.AtPrime (q.val.under (Laurent S)))
      (ScalarCokernel (LocalPointFibre (S := S) p (q.val.under (Laurent S)))
        (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b)) ≠ ⊤ := by
    rw [localPointFibre_cokernel_length p b h₂ hb q]
    exact iteratedPointFibre_length_ne_top p q
  have he := principalCokernel_associativity
    (M := LocalPointFibre (S := S) p (q.val.under (Laurent S)))
    (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b)
    (localOriginalScalar_mem_maximalIdeal b hbz q.val)
    (localPointFibre_scalar_regular_flat p b hb0 _) hlen
  have hs := minimalSum_eq_composition_of_dominant p
    (fun Q hQ => minimalFibre_dominant p Q hQ) b h₂ hb q
  rw [localPointFibre_cokernel_length p b h₂ hb q] at he
  exact hs.symm.trans he.symm

theorem doubleLength_flat_at_under
    [Module.Flat S T] (p : FiniteDominantPrime R) (r : FiniteDominantPrime S) (q :
      FiniteDominantPrime T)
    (hr : q.val.under (Laurent S) = r.val) :
    doubleFibreLength (S := S) p q = quotientFibreLength (S := S) p r *
      residueFibreLength (R := S) q.val := by
  let I := p.val.map (coefficientMap (algebraMap R S))
  let C := Laurent S ⧸ I
  let : CommRing (Localization.AtPrime q.val) := inferInstance
  let : AddCommGroup (Localization.AtPrime q.val ⊗[Laurent T]
    (Laurent T ⧸ I.map (coefficientMap (algebraMap S T)))) := inferInstance
  let : AddCommGroup (Localization.AtPrime q.val ⊗[Laurent S] C) := inferInstance
  let : Module.Flat (Laurent S) (Laurent T) := laurent_flat_baseChange
  let e : (Localization.AtPrime q.val ⊗[Laurent T]
      (Laurent T ⧸ I.map (coefficientMap (algebraMap S T)))) ≃ₗ[Localization.AtPrime q.val]
      (Localization.AtPrime q.val ⊗[Laurent S] C) :=
    ((Ideal.qoutMapEquivTensorQout (I := I) (Laurent T)).baseChange
    (Laurent T) (Localization.AtPrime q.val) _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (Laurent S) (Laurent T)
        (Localization.AtPrime q.val) (Localization.AtPrime q.val) C)
  have h := e.length_eq.trans (localized_length_flat_baseChange C q.val)
  change doubleFibreLength (S := S) p q =
    Module.length (Localization.AtPrime (q.val.under (Laurent S)))
      (Localization.AtPrime (q.val.under (Laurent S)) ⊗[Laurent S] C) *
        residueFibreLength (R := S) q.val at h
  let F : PrimeSpectrum (Laurent S) → ℕ∞ := fun P =>
    Module.length (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime P.asIdeal ⊗[Laurent S] C)
  have hc : F ⟨q.val.under (Laurent S), inferInstance⟩ = F ⟨r.val, inferInstance⟩ :=
    congrArg F (PrimeSpectrum.ext hr)
  exact h.trans (congrArg (fun n : ℕ∞ => n * residueFibreLength (R := S) q.val) hc)

theorem localizedQuotientLength_zero_of_not_le (I : Ideal (Laurent T)) (q : FiniteDominantPrime T)
    (hI : ¬ I ≤ q.val) :
    Module.length (Localization.AtPrime q.val)
      (Localization.AtPrime q.val ⊗[Laurent T] (Laurent T ⧸ I)) = 0 := by
  rw [Module.length_eq_zero_iff]
  let e := IsLocalizedModule.iso q.val.primeCompl
    (TensorProduct.mk (Laurent T) (Localization.AtPrime q.val) (Laurent T ⧸ I) 1)
  have hn : ¬ Nontrivial (LocalizedModule q.val.primeCompl (Laurent T ⧸ I)) := by
    change ¬ (⟨q.val, inferInstance⟩ : PrimeSpectrum (Laurent T)) ∈
      Module.support (Laurent T) (Laurent T ⧸ I)
    rwa [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  let : Subsingleton (LocalizedModule q.val.primeCompl (Laurent T ⧸ I)) :=
    not_nontrivial_iff_subsingleton.mp hn
  exact e.symm.injective.subsingleton

/-- Flat second pullback recovers the actual double fibre coefficient, with
the first minimal-support closure kept explicit. It applies both to a first
field extension and to the actual principal simplex faces. -/
theorem then_flat_coeff
    [Module.Flat S T] [IsNoetherianRing S] [IsNoetherianRing T]
    (p : FiniteDominantPrime R)
    (hdom : ∀ Q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes,
      Q.under S = ⊥) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T)
      (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p))) =
        ((doubleFibreLength (S := S) p q).toNat : ℤ) := by
  classical
  let I := p.val.map (coefficientMap (algebraMap R S))
  let J := I.map (coefficientMap (algebraMap S T))
  let := quotientBaseChange_finite (S := S) p.val
  let := quotientBaseChange_finite (S := T) I
  by_cases hJ : J ≤ q.val
  · let : Module.Flat (Laurent S) (Laurent T) := laurent_flat_baseChange
    have hmin : q.val.under (Laurent S) ∈ I.minimalPrimes :=
      minimalPrime_map_under I q.val
        (minimal_of_finite_quotient_le J q.val q.under_eq_bot hJ)
    let r : FiniteDominantPrime S := ⟨q.val.under (Laurent S), inferInstance,
      minimalFibre_finite p _ hmin, hdom _ hmin⟩
    have hc := flatPullback_coeff_of_under
      (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p)) r q rfl
    rw [quotientFibreCycleMap_of_coeff] at hc
    rw [quotientCycle_eq_flatPullback]
    have hl := congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (doubleLength_flat_at_under p r q rfl)
    simp only [ENat.toNat_mul, Nat.cast_mul] at hl
    exact hc.trans hl.symm
  · have hz : doubleFibreLength (S := S) p q = 0 :=
      localizedQuotientLength_zero_of_not_le J q hJ
    rw [hz]
    simp only [ENat.toNat_zero, Nat.cast_zero]
    rw [quotientFibreCycleMap_coeff]
    apply Finset.sum_eq_zero
    intro r hr
    have hI := (quotientFibreCycleMap_of_support p r).mp hr
    have hnot : ¬ r.val.map (coefficientMap (algebraMap S T)) ≤ q.val :=
      fun h => hJ ((Ideal.map_mono hI).trans h)
    have hm : quotientFibreMultiplicity (S := T) r q = 0 := by
      by_contra hn
      exact hnot ((quotientFibreMultiplicity_ne_zero_iff r q).mp hn)
    simp only [hm, Nat.cast_zero, mul_zero]

end AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
