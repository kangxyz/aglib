/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.DVRGeometricFiniteModel
public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionStability

/-!
# Finite models retaining the intrinsic DVR coefficient condition

The finite residue basis is selected in the actual quotient B / q. Its native
parameter DVR and the finite model both live in Type (max u v), without ULift.
Only the existing monic finite-model construction is used; the completion
condition follows from the actual parameter-localization stability theorem.
-/

@[expose] public noncomputable section
universe u v
namespace DVRGeometricLocalHenselization
open IsLocalRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (B : Type v) [CommRing B] [Algebra R B]
variable (q : Ideal B) [q.IsPrime]
variable (hq : q.comap (algebraMap R B) = maximalIdeal R)
variable (π : R) [Fact (Irreducible π)]

include hq π in
/-- Every vertical prime of a finite-type DVR algebra admits a constructed
finite local model over an actual parameter DVR's polynomial-origin
henselization. The coefficient inclusion is injective. The intrinsic completion
condition is obtained for this actual parameter DVR by parameter stability. -/
theorem exists_finite_origin_model_with_uniformizer_of_geometricallyReducedFractionCompletion
    [Algebra.FiniteType R B]
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R) :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : IsDomain S)
      (_ : IsDiscreteValuationRing S) (_ : Algebra R S),
      Function.Injective (algebraMap R S) ∧
      AdicCompletion.HasGeometricallyReducedFractionCompletion S ∧
      ∃ (n : ℕ) (A : Type (max u v)) (_ : CommRing A)
        (_ : Algebra (Henselization (PolynomialLocalRing S n)) A)
        (_ : Module.Finite (Henselization (PolynomialLocalRing S n)) A) (_ : IsLocalRing A),
        Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  classical
  obtain ⟨n, ⟨G⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType R B)
  let z : Fin n → B := G.val
  have hz : Algebra.adjoin R (Set.range z) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 G.aeval_val_surjective
  let := LocalResidueParameterBasis.residueAlgebra q hq
  obtain ⟨s, hs, t, ht, hb⟩ := LocalResidueParameterBasis.exists_residue_basis q hq z hz
  let : Finite s := hs.to_subtype
  let parameters : s → B := fun a => z (t a)
  have hparameters : IsTranscendenceBasis (ResidueField R)
      (fun a => Ideal.Quotient.mk q (parameters a)) := by
    simpa only [parameters, ht] using hb
  let S := ParameterLocalization.Ring R s π
  let : IsDiscreteValuationRing S := ParameterLocalization.isDiscreteValuationRing R s π
  obtain ⟨A, hA, aA, fA, lA, eA⟩ :=
    exists_finite_model_of_residue_basis R B q hq π z hz parameters hparameters
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    ParameterLocalization.algebraMap_injective R s π,
    ParameterLocalization.hasGeometricallyReducedFractionCompletion R s π hcoeff,
    n, A, hA, aA, fA, lA, eA⟩

include hq in
/-- The uniformizer is supplied by the DVR itself, not by a final theorem premise. -/
theorem exists_finite_origin_model_of_geometricallyReducedFractionCompletion
    [Algebra.FiniteType R B]
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R) :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : IsDomain S)
      (_ : IsDiscreteValuationRing S) (_ : Algebra R S),
      Function.Injective (algebraMap R S) ∧
      AdicCompletion.HasGeometricallyReducedFractionCompletion S ∧
      ∃ (n : ℕ) (A : Type (max u v)) (_ : CommRing A)
        (_ : Algebra (Henselization (PolynomialLocalRing S n)) A)
        (_ : Module.Finite (Henselization (PolynomialLocalRing S n)) A) (_ : IsLocalRing A),
        Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : Fact (Irreducible π) := ⟨hπ⟩
  exact exists_finite_origin_model_with_uniformizer_of_geometricallyReducedFractionCompletion
    R B q hq π hcoeff

end DVRGeometricLocalHenselization
