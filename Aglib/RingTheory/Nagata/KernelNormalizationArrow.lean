/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.InjectiveNormalizationMap
public import Aglib.RingTheory.Nagata.ClosedSupportNormalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Normalizing the actual kernel quotient on both axes

For an arbitrary arrow to a domain, first quotient its actual kernel. The
resulting injection induces the original fraction-field and normalization
maps. Nagata supplies finiteness on both axes; source arithmetic finite type
supplies its Nagata hypothesis internally. The source map only covers its
actual kernel closed subset, not the whole original source spectrum. No
pointed etale cover descent is asserted.
-/

@[expose] public noncomputable section
namespace RingHom.KernelNormalization
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] (f : A →+* B)

/-- The source modulo the actual kernel of the ring homomorphism. -/
abbrev sourceDomain := A ⧸ RingHom.ker f

instance sourceDomain_isDomain : IsDomain (sourceDomain f) := by
  let : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  infer_instance

/-- The normalization of the source kernel quotient in its fraction field. -/
abbrev sourceNormal := integralClosure (sourceDomain f) (FractionRing (sourceDomain f))
/-- The normalization of the target in its fraction field. -/
abbrev targetNormal := integralClosure B (FractionRing B)

/-- The original source map factors through its actual kernel, then normalization. -/
def sourceMap : A →+* sourceNormal f :=
  (algebraMap (sourceDomain f) (sourceNormal f)).comp (Ideal.Quotient.mk (RingHom.ker f))

/-- The actual normalization arrow extending the injective kernel quotient map. -/
def normalMap : sourceNormal f →+* targetNormal (B := B) :=
  integralClosure.mapOfInjective f.kerLift f.kerLift_injective

theorem normalMap_injective : Function.Injective (normalMap f) :=
  integralClosure.mapOfInjective_injective f.kerLift f.kerLift_injective

/-- The two-axis square preserves the original arrow, including its nonzero kernel. -/
theorem normalMap_sourceMap :
    (normalMap f).comp (sourceMap f) = (algebraMap B (targetNormal (B := B))).comp f := by
  rw [normalMap, sourceMap, ← RingHom.comp_assoc,
    integralClosure.mapOfInjective_algebraMap, RingHom.comp_assoc]
  congr 1

/-- Nagata proves the actual source map finite, without normal-finite assumptions. -/
theorem sourceMap_finite (hA : IsNagataRing.{u, 0} A) : (sourceMap f).Finite := by
  have hfin := (integralClosure.normal_model_of_nagata
    (sourceDomain f) (hA.quotient (RingHom.ker f))).1
  exact (RingHom.finite_algebraMap.mpr hfin).comp
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

/-- The actual source normal model retains the original source rank bound. -/
theorem sourceNormal_ringKrullDim_le (hA : IsNagataRing.{u, 0} A) :
    ringKrullDim (sourceNormal f) ≤ ringKrullDim A :=
  (sourceMap_finite f hA).to_isIntegral.ringKrullDim_le

/-- Arithmetic stage finiteness supplies source normalization finiteness internally. -/
theorem sourceMap_finite_of_finiteType_int [Algebra.FiniteType ℤ A] :
    (sourceMap f).Finite := sourceMap_finite f (IsNagataRing.of_finiteType_int A)

/-- Complete source-normal properties over the actual kernel quotient. -/
theorem sourceNormal_properties (hA : IsNagataRing.{u, 0} A) :
    IsNoetherianRing (sourceNormal f) ∧ IsIntegrallyClosed (sourceNormal f) ∧
      Function.Surjective (PrimeSpectrum.comap
        (algebraMap (sourceDomain f) (sourceNormal f))) := by
  have h := integralClosure.normal_model_of_nagata
    (sourceDomain f) (hA.quotient (RingHom.ker f))
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The finite source normalization covers exactly the actual kernel closed
subset. It is not asserted surjective onto the whole original source spectrum. -/
theorem sourceMap_comap_range (hA : IsNagataRing.{u, 0} A) (q : PrimeSpectrum A) :
    q ∈ Set.range (PrimeSpectrum.comap (sourceMap f)) ↔ RingHom.ker f ≤ q.asIdeal := by
  have hsur := (sourceNormal_properties f hA).2.2
  have hrange : Set.range (PrimeSpectrum.comap (sourceMap f)) =
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (RingHom.ker f))) := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨PrimeSpectrum.comap (algebraMap (sourceDomain f) (sourceNormal f)) z, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, hw⟩ := hsur z
      refine ⟨w, ?_⟩
      change PrimeSpectrum.comap (Ideal.Quotient.mk (RingHom.ker f))
        (PrimeSpectrum.comap (algebraMap (sourceDomain f) (sourceNormal f)) w) = q
      exact (congrArg (PrimeSpectrum.comap (Ideal.Quotient.mk (RingHom.ker f))) hw).trans hz
  rw [hrange, _root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  all_goals rfl

/-- Complete target-normal data and rank, from its actual Nagata source. -/
theorem targetNormal_properties (hB : IsNagataRing.{u, 0} B) :
    Module.Finite B (targetNormal (B := B)) ∧
    IsNoetherianRing (targetNormal (B := B)) ∧
    IsIntegrallyClosed (targetNormal (B := B)) ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (targetNormal (B := B)))) ∧
    ringKrullDim (targetNormal (B := B)) ≤ ringKrullDim B :=
  integralClosure.normal_model_of_nagata B hB

end RingHom.KernelNormalization
