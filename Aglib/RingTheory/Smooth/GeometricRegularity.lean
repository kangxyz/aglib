/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.Smooth.GeometricRegularity.LocalCriterion
public import Aglib.RingTheory.Smooth.GeometricRegularity.RegularLocalKernel
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Geometric regularity implies smoothness over a field

A finite type regular algebra over a perfect field is smooth. We prove this
on localized polynomial presentations: regularity supplies the intersection
identity for the kernel, and formal smoothness of the residue field supplies
the remaining injection in the Jacobian criterion.

For an arbitrary field, regularity after base change to an algebraic closure
therefore implies smoothness after that base change. Faithfully flat descent
then gives smoothness over the original field.
-/

@[expose] public section
noncomputable section
open TensorProduct IsLocalRing KaehlerDifferential
universe u
namespace Algebra
variable (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]

/-- Over a perfect field, a regular localization of a finite type algebra is
formally smooth. -/
lemma IsSmoothAt.of_isRegularLocalRing_of_perfectField [PerfectField k]
    (p : Ideal A) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] :
    IsSmoothAt k p := by
  let S := Localization.AtPrime p
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  let q : Ideal (MvPolynomial (Fin n) k) := p.comap f₀.toRingHom
  let P := Localization.AtPrime q
  let fP : P →ₐ[k] S := IsLocalization.liftAlgHom (M := q.primeCompl)
    (f := (IsScalarTower.toAlgHom k A S).comp f₀) fun x ↦ by
      simpa using IsLocalization.map_units (M := p.primeCompl) S ⟨f₀ x.1, x.2⟩
  have hfP : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := q.primeCompl) P x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  algebraize [fP.toRingHom]
  have : IsScalarTower k P S := .of_algebraMap_eq' fP.comp_algebraMap.symm
  have : FormallyEtale (MvPolynomial (Fin n) k) P := .of_isLocalization q.primeCompl
  have : FormallySmooth k P := .comp _ (MvPolynomial (Fin n) k) _
  have : Module.Free P Ω[P⁄k] :=
    .of_equiv (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) P)
  have : Algebra.EssFiniteType (MvPolynomial (Fin n) k) P :=
    .of_isLocalization _ q.primeCompl
  have : Algebra.EssFiniteType k P := .comp _ (MvPolynomial (Fin n) k) _
  have : Algebra.EssFiniteType A S := .of_isLocalization _ p.primeCompl
  have : Algebra.EssFiniteType k S := .comp _ A _
  have : Algebra.EssFiniteType k (ResidueField S) := .comp _ S _
  have : IsRegularLocalRing P := inferInstance
  have : IsRegularLocalRing (P ⧸ RingHom.ker (algebraMap P S)) :=
    IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hfP).symm
  apply FormallySmooth.of_ker_inf_maximalIdeal_sq (P := P) hfP
    (Ideal.fg_of_isNoetherianRing _)
  exact (IsRegularLocalRing.inf_maximalIdeal_sq_eq_mul P _).le

/-- A finite type regular algebra over a perfect field is smooth. -/
theorem Smooth.of_isRegularRing_of_perfectField [PerfectField k] [IsRegularRing A] :
    Algebra.Smooth k A := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨(smoothLocus_eq_univ_iff).mp ?_, inferInstance⟩
  exact Set.eq_univ_of_forall fun p ↦ IsSmoothAt.of_isRegularLocalRing_of_perfectField k A p.asIdeal

/-- A finite type algebra over a field is smooth if every field base change is regular. -/
theorem Smooth.of_geometricallyRegular
    (h : ∀ (K : Type u) [Field K] [Algebra k K], IsRegularRing (K ⊗[k] A)) :
    Algebra.Smooth k A := by
  have : IsRegularRing (AlgebraicClosure k ⊗[k] A) := h (AlgebraicClosure k)
  have : Algebra.Smooth (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A) :=
    Smooth.of_isRegularRing_of_perfectField _ _
  exact Smooth.of_smooth_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)
end Algebra
