/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteDecomposition
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # The actual selected local factor of a finite-etale normalization

Localization of the original integral closure at a specified maximal ideal
is a DVR. A finite product decomposition is used only inside the proof; the
output ring remains the specified localization. Over a Henselian base its
original localization map is surjective and the same ring is finite.
-/

@[expose] public noncomputable section

namespace integralClosure

universe u v w

private theorem exists_dvr_equiv_localization_of_pi
    {C : Type w} [CommRing C] {ι : Type w} [Finite ι]
    (D : ι → Type w) [∀ i, CommRing (D i)]
    [∀ i, IsDedekindDomain (D i)] (hfield : ∀ i, ¬ IsField (D i))
    (E : C ≃+* ∀ i, D i) (q : Ideal C) [q.IsMaximal] :
    ∃ (T : Type w) (_ : CommRing T) (_ : IsDomain T) (_ : IsDiscreteValuationRing T),
      Nonempty (Localization.AtPrime q ≃+* T) := by
  let P : Ideal (∀ i, D i) := q.comap E.symm.toRingHom
  let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv E.symm
  obtain ⟨i, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨P, inferInstance⟩ : PrimeSpectrum (∀ i, D i))
  have hp' : p.asIdeal.comap (Pi.evalRingHom D i) = P :=
    congrArg PrimeSpectrum.asIdeal hp
  let f := Pi.evalRingHom D i
  have hpmax : p.asIdeal.IsMaximal := by
    have hm := Ideal.map_eq_top_or_isMaximal_of_surjective f
      (Function.surjective_eval i) (inferInstance : P.IsMaximal)
    rw [← hp', Ideal.map_comap_of_surjective f (Function.surjective_eval i)] at hm
    exact hm.resolve_left p.isPrime.ne_top
  have hpne : p.asIdeal ≠ ⊥ := by
    intro h
    exact hfield i (Ring.isField_iff_maximal_bot.mpr (h ▸ hpmax))
  let T := Localization.AtPrime p.asIdeal
  let : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (D i) hpne T
  have hq : q = P.comap E.toRingHom := by
    ext x
    change x ∈ q ↔ E.symm (E x) ∈ q
    rw [E.symm_apply_apply]
  let e₁ := Localization.localRingEquiv q P E hq
  let e₂ := Localization.localRingEquiv P
    (p.asIdeal.comap f) (RingEquiv.refl _) hp'.symm
  let e₃ := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom p.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective p.asIdeal)
  exact ⟨T, inferInstance, inferInstance, inferInstance, ⟨e₁.trans (e₂.trans e₃)⟩⟩

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type w) [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]
  (q : Ideal (integralClosure R A)) [q.IsMaximal]

include K

private theorem exists_dvr_equiv_localization :
    ∃ (D : Type w) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D),
      Nonempty (Localization.AtPrime q ≃+* D) := by
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
  let (i : ι) : IsDedekindDomain (integralClosure R (L i)) :=
    integralClosure.isDedekindDomain R K (L i)
  apply exists_dvr_equiv_localization_of_pi (fun i => integralClosure R (L i)) _
    (integralClosure.equivPi R A L (e.restrictScalars R)).toRingEquiv q
  intro i hfield
  apply IsDiscreteValuationRing.not_isField R
  apply isField_of_isIntegral_of_isField (S := integralClosure R (L i)) ?_ hfield
  intro x y hxy
  apply IsFractionRing.injective R K
  apply (algebraMap K (L i)).injective
  have h := congrArg (algebraMap (integralClosure R (L i)) (L i)) hxy
  simpa only [← IsScalarTower.algebraMap_apply] using h

/-- The specified localization of the original normalization is a domain. -/
theorem localizationAtPrime_isDomain : IsDomain (Localization.AtPrime q) := by
  obtain ⟨D, _, _, _, ⟨e⟩⟩ := exists_dvr_equiv_localization R K A q
  exact MulEquiv.isDomain D e.toMulEquiv

/-- The same specified localization is a DVR. No Henselianity of the base is needed. -/
theorem localizationAtPrime_isDiscreteValuationRing :
    letI := localizationAtPrime_isDomain R K A q
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  let := localizationAtPrime_isDomain R K A q
  obtain ⟨D, _, _, _, ⟨e⟩⟩ := exists_dvr_equiv_localization R K A q
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm

/-- Henselianity makes the original localization map onto the specified factor
surjective; no replacement product factor is exposed. -/
theorem localizationAtPrime_algebraMap_surjective [HenselianLocalRing R] :
    Function.Surjective (algebraMap (integralClosure R A) (Localization.AtPrime q)) := by
  let : Module.Finite R (integralClosure R A) := finite_of_etale R K A
  exact HenselianLocalRing.algebraMap_localizationAtPrime_surjective
    R (integralClosure R A) q

/-- The actual selected localization is finite over the Henselian base. -/
theorem localizationAtPrime_finite [HenselianLocalRing R] :
    Module.Finite R (Localization.AtPrime q) := by
  let : Module.Finite R (integralClosure R A) := finite_of_etale R K A
  exact HenselianLocalRing.finite_localizationAtPrime R (integralClosure R A) q

end integralClosure
