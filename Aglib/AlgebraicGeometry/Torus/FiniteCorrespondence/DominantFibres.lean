/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.FlatMultiplicity
public import Aglib.RingTheory.Flat.TorsionFreeBaseChange
public import Aglib.RingTheory.Ideal.MinimalPrime.FlatBaseChange
public import Aglib.RingTheory.Localization.LengthFlatBaseChange

/-!
# DominantFibres for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `DominantFibres.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`feb98980155e255608042440f62d140ae61d399b41ffda5ff4f2a096da2dfc0e`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The literal quotient of the scalar-extended Laurent algebra. -/
def quotientBaseChangeEquiv (I : Ideal (Laurent R)) :
    S ⊗[R] (Laurent R ⧸ I) ≃ₐ[S]
      Laurent S ⧸ I.map (coefficientMap (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Laurent R) S I).trans
    (Ideal.quotientEquivAlg _ _ (MonoidAlgebra.scalarTensorEquiv R S)
      (by
        have hmap := Ideal.map_map (I := I)
          (Algebra.TensorProduct.includeRight : Laurent R →ₐ[R] S ⊗[R] Laurent R).toRingHom
          (MonoidAlgebra.scalarTensorEquiv R S (M := Character)).toRingHom
        have hcoeff := congrArg (fun f : Laurent R →+* Laurent S => I.map f)
          (scalarTensorEquiv_includeRight (R := R) (S := S))
        exact (hmap.trans hcoeff).symm))

theorem quotientBaseChange_finite (I : Ideal (Laurent R)) [Module.Finite R (Laurent R ⧸ I)] :
    Module.Finite S (Laurent S ⧸ I.map (coefficientMap (algebraMap R S))) :=
  Module.Finite.of_surjective (quotientBaseChangeEquiv (S := S) I).toLinearMap
    (quotientBaseChangeEquiv I).surjective

theorem pointQuotient_baseChange_torsionFree [IsDomain R] [Module.Flat R S] (p :
    FiniteDominantPrime R) :
    Module.IsTorsionFree S (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) := by
  let := MonoidAlgebra.FiniteDominantPrime.quotient_torsionFree p
  let := _root_.Module.torsionFree_baseChange (R := R) (S := S) (Laurent R ⧸ p.val)
  exact (quotientBaseChangeEquiv (S := S) p.val).symm.injective.moduleIsTorsionFree _
    (fun s x => (quotientBaseChangeEquiv p.val).symm.toLinearEquiv.map_smul s x)

/-- Every minimal fibre component is dominant over the new base. This is
derived from torsion-freeness, without imposing flatness on the point quotient. -/
theorem minimalFibre_dominant [IsDomain R] [IsDomain S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) :
    q.under S = ⊥ := by
  let C := Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))
  let : Module.IsTorsionFree S C := pointQuotient_baseChange_torsionFree p
  have hq' : q ∈ (Module.annihilator (Laurent S) C).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  ext s
  rw [Ideal.mem_bot]
  change algebraMap S (Laurent S) s ∈ q ↔ s = 0
  constructor
  · intro hs
    by_contra hs0
    have hreg : IsSMulRegular C (algebraMap S (Laurent S) s) := by
      intro x y hxy
      apply (IsRegular.of_ne_zero hs0).isSMulRegular (M := C)
      simpa only [algebraMap_smul] using hxy
    exact hreg.notMem_of_mem_minimalPrimes hq' hs
  · rintro rfl; simp

theorem minimalFibre_finite (p : FiniteDominantPrime R) (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) :
    Module.Finite S (Laurent S ⧸ q) := by
  let := quotientBaseChange_finite (S := S) p.val
  exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ S hq.le).toLinearMap
    (Ideal.Quotient.factor_surjective hq.le)

/-- All minimal components of the literal fibre give actual target cycle labels. -/
def minimalFibrePoint [IsDomain R] [IsDomain S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) : FiniteDominantPrime
      S :=
  ⟨q, hq.isPrime, minimalFibre_finite p q hq, minimalFibre_dominant p q hq⟩

theorem minimalFibre_under [Module.Flat R S] (p : FiniteDominantPrime R) (q : Ideal (Laurent S))
    (hq : q ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes) :
    q.under (Laurent R) = p.val := by
  let : Module.Flat (Laurent R) (Laurent S) := laurent_flat_baseChange
  have h := _root_.Ideal.minimalPrime_map_under p.val q hq
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h
  exact Set.mem_singleton_iff.mp h

/-- A dominant prime over any finite quotient algebra is a minimal component. -/
theorem minimal_of_finite_quotient_le (I : Ideal (Laurent S))
    [Module.Finite S (Laurent S ⧸ I)] (q : Ideal (Laurent S)) [q.IsPrime]
    (hq : q.under S = ⊥) (hI : I ≤ q) : q ∈ I.minimalPrimes := by
  let Q : Ideal (Laurent S ⧸ I) := q.map (Ideal.Quotient.mk I)
  let : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hI
  have hQB : Q.under (Laurent S) = q := Ideal.comap_map_mk hI
  have hQS : Q.under S = ⊥ := by
    rw [← Ideal.under_under (A := S) (B := Laurent S) Q, hQB, hq]
  have hQ : Q ∈ minimalPrimes (Laurent S ⧸ I) := by
    have h := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := S) Q
    simpa [hQS] using h
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨Q, hQ, hQB⟩

theorem fibre_under_iff_minimal [Module.Flat R S] (p : FiniteDominantPrime R) (q :
    FiniteDominantPrime S) :
    q.val.under (Laurent R) = p.val ↔
      q.val ∈ (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes := by
  constructor
  · intro h
    let := quotientBaseChange_finite (S := S) p.val
    apply minimal_of_finite_quotient_le _ q.val q.under_eq_bot
    apply Ideal.map_le_iff_le_comap.mpr
    change p.val ≤ q.val.under (Laurent R)
    rw [h]
  · exact minimalFibre_under p q.val

theorem finite_minimalFibre [IsNoetherianRing S] (p : FiniteDominantPrime R) :
    (p.val.map (coefficientMap (algebraMap R S))).minimalPrimes.Finite := by
  let := quotientBaseChange_finite (S := S) p.val
  let : IsNoetherianRing (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) :=
    IsNoetherianRing.of_finite S _
  rw [Ideal.minimalPrimes_eq_comap]
  exact (minimalPrimes.finite_of_isNoetherianRing _).image _

theorem finite_dominantFibre [IsNoetherianRing S] [Module.Flat R S] (p : FiniteDominantPrime R) :
    {q : FiniteDominantPrime S | q.val.under (Laurent R) = p.val}.Finite := by
  apply ((finite_minimalFibre (S := S) p).preimage
    (f := fun q : FiniteDominantPrime S => q.val) Subtype.val_injective.injOn).subset
  intro q hq
  exact (fibre_under_iff_minimal p q).mp hq

end AlgebraicGeometry.Torus.FiniteCorrespondence
