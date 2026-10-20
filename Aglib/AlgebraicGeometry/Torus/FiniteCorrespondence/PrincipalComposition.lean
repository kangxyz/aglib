/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalDominance
public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalAssociativity
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
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Interchange
public import Aglib.RingTheory.Localization.IteratedModuleLength
public import Aglib.RingTheory.Support.Localization
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalFibres

/-!
# PrincipalComposition for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `PrincipalComposition.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`30e9c8c05b917cd79eee9b811cbbb7933606658ac91cc473b58e99be46350a8b`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

open _root_.Module
  (ScalarCokernel iterated_localized_length localized_minimalSupport_iff mem_moduleMinimalPrimes
    minimalPrimeCokernelTerm moduleMinimalPrimes principalEuler
    principalEuler_associativity_of_minimalRegular scalarCokernelEquiv
    scalar_regular_primeQuotient)



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
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T]

local instance laurentSelf_finite : Module.Finite (Laurent S) (Laurent S) := Module.Finite.self _

/-- The literal first prime-quotient fibre, localized at a final target contraction. -/
abbrev LocalPointFibre (p : FiniteDominantPrime R) (Q : Ideal (Laurent S)) [Q.IsPrime] :=
  Localization.AtPrime Q ⊗[Laurent S]
    (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S)))

/-- The generic coefficient expansion uses every cycle label, without requiring an
object realization or surjectivity of the object-cycle homomorphism. -/
theorem quotientFibreCycleMap_coeff [IsNoetherianRing T]
    (z : FreeAbelianGroup (FiniteDominantPrime S)) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T) z) =
      ∑ r ∈ z.support,
        FreeAbelianGroup.coeff r z * (quotientFibreMultiplicity (S := T) r q : ℤ) := by
  conv_lhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of z]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_zsmul, map_zsmul, quotientFibreCycleMap_of_coeff]
  exact smul_eq_mul _ _

/-- A local minimal prime of the first fibre contracts to an actual minimal
prime of the first literal specialization. -/
theorem localPointFibre_minimal_under (p : FiniteDominantPrime R)
    (Q : Ideal (Laurent S)) [Q.IsPrime]
    (r : Ideal (Localization.AtPrime Q)) [r.IsPrime]
    (hr : r ∈ (Module.annihilator (Localization.AtPrime Q)
      (LocalPointFibre (S := S) p Q)).minimalPrimes) :
    r.under (Laurent S) ∈
      (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes := by
  have h := (localized_minimalSupport_iff
    (M := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) Q r).mp hr
  rwa [Ideal.annihilator_quotient] at h

/-- Nonzero second base scalar is regular on the local minimal prime factors.
The first fibre module itself may have scalar torsion. -/
theorem localPointFibre_minimal_regular [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (p : FiniteDominantPrime R) (a : R) (h : Function.Surjective (algebraMap R S))
    (ha : RingHom.ker (algebraMap R S) = Ideal.span ({a} : Set R))
    (Q : Ideal (Laurent S)) [Q.IsPrime] (b : S) (hb : b ≠ 0)
    (r : Ideal (Localization.AtPrime Q))
    (hr : r ∈ (Module.annihilator (Localization.AtPrime Q)
      (LocalPointFibre (S := S) p Q)).minimalPrimes) :
    IsSMulRegular (Localization.AtPrime Q ⧸ r)
      (algebraMap S (Localization.AtPrime Q) b) := by
  let := hr.isPrime
  have hmin := localPointFibre_minimal_under p Q r hr
  have hd := principalPoint_minimal_contract_zero p a h ha (r.under (Laurent S)) hmin
  apply scalar_regular_primeQuotient
  intro hin
  rw [IsScalarTower.algebraMap_apply S (Laurent S) (Localization.AtPrime Q)] at hin
  change b ∈ (r.under (Laurent S)).under S at hin
  rw [hd, Ideal.mem_bot] at hin
  exact hb hin

/-- Scalar-cokernel length on the first localized quotient is the literal
second specialization length. This requires no regularity of the first fibre. -/
theorem localPointFibre_cokernel_length (p : FiniteDominantPrime R) (b : S)
    (h : Function.Surjective (algebraMap S T))
    (hb : RingHom.ker (algebraMap S T) = Ideal.span ({b} : Set S))
    (q : FiniteDominantPrime T) :
    Module.length (Localization.AtPrime (q.val.under (Laurent S)))
      (ScalarCokernel (LocalPointFibre (S := S) p (q.val.under (Laurent S)))
        (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b)) =
    Module.length (Localization.AtPrime q.val)
      (Localization.AtPrime q.val ⊗[Laurent T]
        (Laurent T ⧸ (p.val.map (coefficientMap (algebraMap R S))).map
          (coefficientMap (algebraMap S T)))) := by
  let I := p.val.map (coefficientMap (algebraMap R S))
  let B := Localization.AtPrime (q.val.under (Laurent S))
  let e : (B ⧸ I.map (algebraMap (Laurent S) B)) ≃ₗ[B]
      LocalPointFibre (S := S) p (q.val.under (Laurent S)) :=
    Ideal.qoutMapEquivTensorQout B
  rw [← (scalarCokernelEquiv e (algebraMap S B b)).length_eq]
  have he := localized_principalPrimeCokernel_length I
    (algebraMap S (Laurent S) b) (laurentCoefficient_surjective h)
    (laurentCoefficient_ker_principal b hb) q.val
  rw [← IsScalarTower.algebraMap_apply S (Laurent S) B b] at he
  exact he

/-- The double literal quotient has finite local length at an actual final
cycle label, including the zero fibre. -/
theorem iteratedPointFibre_length_ne_top [IsNoetherianRing T]
    (p : FiniteDominantPrime R) (q : FiniteDominantPrime T) :
    Module.length (Localization.AtPrime q.val)
      (Localization.AtPrime q.val ⊗[Laurent T]
        (Laurent T ⧸ (p.val.map (coefficientMap (algebraMap R S))).map
          (coefficientMap (algebraMap S T)))) ≠ ⊤ := by
  classical
  let I := p.val.map (coefficientMap (algebraMap R S))
  let J := I.map (coefficientMap (algebraMap S T))
  let := quotientBaseChange_finite (S := S) p.val
  let := quotientBaseChange_finite (S := T) I
  let : IsNoetherianRing (Laurent T ⧸ J) := IsNoetherianRing.of_finite T _
  by_cases hj : J ≤ q.val
  · exact Module.length_localized_quotient_ne_top J q.val
      (minimal_of_finite_quotient_le J q.val q.under_eq_bot hj)
  · have hz : Module.length (Localization.AtPrime q.val)
        (Localization.AtPrime q.val ⊗[Laurent T] (Laurent T ⧸ J)) = 0 := by
      rw [Module.length_eq_zero_iff]
      let e := IsLocalizedModule.iso q.val.primeCompl
        (TensorProduct.mk (Laurent T) (Localization.AtPrime q.val) (Laurent T ⧸ J) 1)
      have hn : ¬ Nontrivial (LocalizedModule q.val.primeCompl (Laurent T ⧸ J)) := by
        change ¬ (⟨q.val, inferInstance⟩ : PrimeSpectrum (Laurent T)) ∈
          Module.support (Laurent T) (Laurent T ⧸ J)
        rwa [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
      let : Subsingleton (LocalizedModule q.val.primeCompl (Laurent T ⧸ J)) :=
        not_nontrivial_iff_subsingleton.mp hn
      exact e.symm.injective.subsingleton
    exact fun ht => ENat.zero_ne_top (hz.symm.trans ht)

/-- Original-prime transport of each actual local Euler factor, without
replacing the first quotient by a flat point object. -/
theorem localPointFibre_minimalTerm_transport (p : FiniteDominantPrime R) (b : S)
    (h : Function.Surjective (algebraMap S T))
    (hb : RingHom.ker (algebraMap S T) = Ideal.span ({b} : Set S))
    (q : FiniteDominantPrime T) (r : Ideal (Localization.AtPrime (q.val.under (Laurent S))))
    (hr : r ∈ (Module.annihilator (Localization.AtPrime (q.val.under (Laurent S)))
      (LocalPointFibre (S := S) p (q.val.under (Laurent S)))).minimalPrimes)
    (z : FiniteDominantPrime S) (hz : z.val = r.under (Laurent S)) :
    minimalPrimeCokernelTerm (LocalPointFibre (S := S) p (q.val.under (Laurent S)))
      (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b) r =
        (quotientFibreMultiplicity (S := S) p z : ℤ) *
          (quotientFibreMultiplicity (S := T) z q : ℤ) := by
  let := hr.isPrime
  have hf := localized_principalPrimeCokernel_length (r.under (Laurent S))
    (algebraMap S (Laurent S) b) (laurentCoefficient_surjective h)
    (laurentCoefficient_ker_principal b hb) q.val
  rw [IsLocalization.map_under (q.val.under (Laurent S)).primeCompl
    (Localization.AtPrime (q.val.under (Laurent S))) r] at hf
  rw [← IsScalarTower.algebraMap_apply S (Laurent S)
    (Localization.AtPrime (q.val.under (Laurent S))) b] at hf
  simp only [minimalPrimeCokernelTerm, dite_eq_left hr]
  rw [iterated_localized_length (M := Laurent S ⧸
    p.val.map (coefficientMap (algebraMap R S))) (q.val.under (Laurent S)) r, hf]
  simp only [quotientFibreMultiplicity, quotientFibreLength]
  rcases z with ⟨z, hzprop⟩
  dsimp only at hz
  subst z
  rfl

/-- The local weighted sum is the literal coefficient of the two maintained
quotient-fibre cycle operators. Proper-support closure supplies all labels. -/
theorem localPointFibre_minimalSum_eq_composition_coeff
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (p : FiniteDominantPrime R) (a : R) (h₁ : Function.Surjective (algebraMap R S))
    (ha : RingHom.ker (algebraMap R S) = Ideal.span ({a} : Set R))
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
    principalPoint_minimal_label p a h₁ ha (r.under (Laurent S))
      (localPointFibre_minimal_under p Q r hm)
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
        minimal_of_finite_quotient_le I z.val z.under_eq_bot
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

/-- Actual composition coefficients are Euler characteristics of the first
fibre localized at the final contraction. No scalar regularity on that fibre,
Cohen--Macaulay property, or point-flatness is assumed. -/
theorem quotientFibreCycleMap_composition_coeff_eq_euler
    [IsNoetherianRing S] [IsNoetherianRing T]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    (p : FiniteDominantPrime R) (a : R) (h₁ : Function.Surjective (algebraMap R S))
    (ha : RingHom.ker (algebraMap R S) = Ideal.span ({a} : Set R))
    (b : S) (hb0 : b ≠ 0) (h₂ : Function.Surjective (algebraMap S T))
    (hb : RingHom.ker (algebraMap S T) = Ideal.span ({b} : Set S)) (q : FiniteDominantPrime T) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := T)
      (quotientFibreCycleMap (S := S) (FreeAbelianGroup.of p))) =
    principalEuler (N := LocalPointFibre (S := S) p (q.val.under (Laurent S)))
      (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b) := by
  have hbz : algebraMap S T b = 0 := by
    apply RingHom.mem_ker.mp
    rw [hb]
    exact Ideal.subset_span (Set.mem_singleton b)
  have hlen : Module.length (Localization.AtPrime (q.val.under (Laurent S)))
      (ScalarCokernel (LocalPointFibre (S := S) p (q.val.under (Laurent S)))
        (algebraMap S (Localization.AtPrime (q.val.under (Laurent S))) b)) ≠ ⊤ := by
    rw [localPointFibre_cokernel_length p b h₂ hb q]
    exact iteratedPointFibre_length_ne_top p q
  rw [principalEuler_associativity_of_minimalRegular _
    (localOriginalScalar_mem_maximalIdeal b hbz q.val) hlen
    (localPointFibre_minimal_regular p a h₁ ha _ b hb0)]
  exact (localPointFibre_minimalSum_eq_composition_coeff p a h₁ ha b h₂ hb q).symm

end AlgebraicGeometry.Torus.FiniteCorrespondence
