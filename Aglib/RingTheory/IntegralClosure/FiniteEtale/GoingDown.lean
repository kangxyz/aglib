/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Going down for the original possibly disconnected normalization

Finite etale generic algebras need not be domains. Their actual normalization
still satisfies going down over the normal base: every prime belongs to one
of the finite generic field factors. No localization is asserted integral.
-/

@[expose] public noncomputable section

namespace integralClosure

private theorem hasGoingDown_of_equiv_pi
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    {ι : Type*} [Finite ι] (D : ι → Type*)
    [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)]
    [∀ i, Algebra.HasGoingDown R (D i)] (e : C ≃ₐ[R] ∀ i, D i) :
    Algebra.HasGoingDown R C := by
  constructor
  intro p hp Q hQ hpQ
  let Q' := Q.comap e.symm.toRingHom
  let : Q'.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨Q', inferInstance⟩ : PrimeSpectrum (∀ i, D i))
  have hq' : q.asIdeal.comap (Pi.evalRingHom D i) = Q' :=
    congrArg PrimeSpectrum.asIdeal hq
  let φ : C →ₐ[R] D i := (Pi.evalAlgHom R D i).comp e.toAlgHom
  have hqC : q.asIdeal.comap φ.toRingHom = Q := by
    change (q.asIdeal.comap (Pi.evalRingHom D i)).comap e.toRingHom = Q
    rw [hq']
    ext x
    change e.symm (e x) ∈ Q ↔ x ∈ Q
    rw [e.symm_apply_apply]
  have hbase (J : Ideal (D i)) : (J.comap φ.toRingHom).under R = J.under R := by
    ext r
    change φ (algebraMap R C r) ∈ J ↔ algebraMap R (D i) r ∈ J
    rw [φ.commutes]
  have hpq : p < q.asIdeal.under R := by
    rw [← hbase q.asIdeal, hqC]
    exact hpQ
  obtain ⟨P, hPq, hP, hPp⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt q.asIdeal hpq
  refine ⟨P.comap φ.toRingHom, ?_, hP.comap _, ⟨?_⟩⟩
  · rw [← hqC]
    exact Ideal.comap_mono hPq
  · rw [hbase]
    exact hPp.over

variable (R K A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

include K in
/-- The original normalization satisfies going down without a domain assumption
on the generic algebra or its normalization. -/
theorem hasGoingDown_of_etale : Algebra.HasGoingDown R (integralClosure R A) := by
  classical
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let := hι
  let := hL
  let := hKL
  let (i : ι) : Algebra R (L i) :=
    ((algebraMap K (L i)).comp (algebraMap R K)).toAlgebra
  let (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  let (i : ι) : Module.Finite K (L i) := (hfin i).1
  let (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  let (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  let (i : ι) : FaithfulSMul R (integralClosure R (L i)) := by
    apply (faithfulSMul_iff_algebraMap_injective R _).mpr
    intro x y hxy
    apply IsFractionRing.injective R K
    apply (algebraMap K (L i)).injective
    have h := congrArg (algebraMap (integralClosure R (L i)) (L i)) hxy
    simpa only [← IsScalarTower.algebraMap_apply] using h
  exact hasGoingDown_of_equiv_pi R (integralClosure R A)
    (fun i => integralClosure R (L i))
    (integralClosure.equivPi R A L (e.restrictScalars R))

end integralClosure
