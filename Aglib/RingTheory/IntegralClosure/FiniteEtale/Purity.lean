/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale
public import Aglib.RingTheory.Etale.ZariskiNagataPurity
public import Aglib.RingTheory.Etale.HeightOneEquiv
public import Mathlib.RingTheory.Etale.Pi

/-! # Purity for the original possibly disconnected normalization

The finite generic field factors are used only inside the proof. Their prime
localizations are the native product-projection localizations, preserving the
specified source heights and formal unramifiedness. Domain purity on these
factors therefore proves etaleness of the unchanged literal normalization.
-/

@[expose] public noncomputable section

namespace Algebra

/-- Unramifiedness in source codimension one passes to each actual product
factor. Projection is localization at its idempotent; the original prime
localization comparison is the native evaluation map. -/
theorem unramified_height_one_pi_factor
    (R : Type*) [CommRing R] {ι : Type*} (S : ι → Type*)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : ∀ q : PrimeSpectrum (∀ i, S i),
      q.asIdeal.height = 1 → IsUnramifiedAt R q.asIdeal) (i : ι) :
    ∀ q : PrimeSpectrum (S i), q.asIdeal.height = 1 → IsUnramifiedAt R q.asIdeal := by
  classical
  let : Algebra (∀ i, S i) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  let : IsLocalization.Away (Pi.single i 1 : ∀ i, S i) (S i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  intro q hq
  let p : PrimeSpectrum (∀ i, S i) := PrimeSpectrum.comap (Pi.evalRingHom S i) q
  have hp : p.asIdeal.height = 1 :=
    (IsLocalization.height_under (Submonoid.powers (Pi.single i 1)) q.asIdeal).trans hq
  let : IsUnramifiedAt R p.asIdeal := h p hp
  exact FormallyUnramified.of_surjective
    (Localization.localAlgHom p.asIdeal q.asIdeal (Pi.evalAlgHom R S i) rfl)
    (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal).surjective

end Algebra

namespace integralClosure

variable (R K A : Type*) [CommRing R] [IsDomain R] [IsRegularRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

include K in
/-- Zariski--Nagata purity for the literal normalization of a finite etale
fraction-field algebra. The generic algebra and its normalization need not be
connected or domains. The hypothesis concerns every height-one prime of the
original normalization, not a supplied factor or an auxiliary model. -/
theorem etale_of_unramified_height_one
    (h : ∀ q : PrimeSpectrum (integralClosure R A),
      q.asIdeal.height = 1 → Algebra.IsUnramifiedAt R q.asIdeal) :
    Algebra.Etale R (integralClosure R A) := by
  classical
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_localization_maximal
    (fun p _ _ => IsRegularLocalRing.isIntegrallyClosed_of_regularLocal (Localization.AtPrime p))
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
  let eB := integralClosure.equivPi R A L (e.restrictScalars R)
  have hpi := Algebra.unramified_height_one_of_equiv eB h
  let (i : ι) : Algebra.Etale R (integralClosure R (L i)) := by
    let : FaithfulSMul R (L i) := FaithfulSMul.trans R K (L i)
    let : Algebra (FractionRing R) (L i) := FractionRing.liftAlgebra R (L i)
    let : IsScalarTower R (FractionRing R) (L i) :=
      FractionRing.isScalarTower_liftAlgebra R (L i)
    let eK := IsLocalization.algEquiv (nonZeroDivisors R) K (FractionRing R)
    let : Algebra.IsSeparable (FractionRing R) (L i) :=
      Algebra.IsSeparable.of_equiv_equiv eK.toRingEquiv (RingEquiv.refl (L i)) (by
        apply IsLocalization.ringHom_ext (nonZeroDivisors R)
        ext r
        change algebraMap (FractionRing R) (L i) (eK (algebraMap R K r)) =
          algebraMap K (L i) (algebraMap R K r)
        rw [eK.commutes, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply])
    let : IsFractionRing (integralClosure R (L i)) (L i) :=
      integralClosure.isFractionRing_of_finite_extension K (L i)
    let : IsIntegrallyClosed (integralClosure R (L i)) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact Algebra.etale_of_unramified_height_one_of_isRegularRing R
      (integralClosure R (L i)) (L i)
      (Algebra.unramified_height_one_pi_factor R (fun j => integralClosure R (L j)) hpi i)
  exact Algebra.Etale.of_equiv eB.symm

end integralClosure
