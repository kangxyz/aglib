/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.AbsoluteIrreducibilitySpecialization
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Geometric integrality of the original hypersurface on a principal open

The scalar extension of the original quotient by `P` is identified with the
quotient by the coefficient image of that same polynomial. The algebra
equivalence preserves the actual structural scalar map. The scheme statements
use the native affine tensor-product square and the original pullback.
No properness, perfectness, or Noetherian hypothesis is imposed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension of the actual principal polynomial quotient, as an
algebra over the actual new coefficient ring. -/
def tensorQuotientSpanSingletonEquiv (P : MvPolynomial σ R) :
    S ⊗[R] (MvPolynomial σ R ⧸ Ideal.span {P}) ≃ₐ[S]
      MvPolynomial σ S ⧸ Ideal.span {map (algebraMap R S) P} := by
  let e := algebraTensorAlgEquiv (σ := σ) R S
  have hI : Ideal.span {map (algebraMap R S) P} =
      ((Ideal.span {P}).map
        (Algebra.TensorProduct.includeRight : MvPolynomial σ R →ₐ[R]
          S ⊗[R] MvPolynomial σ R).toRingHom).map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    change Ideal.span {map (algebraMap R S) P} = Ideal.span {e (1 ⊗ₜ[R] P)}
    simp only [e, algebraTensorAlgEquiv_tmul, one_smul]
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S
    (MvPolynomial σ R) S (Ideal.span {P})).trans (Ideal.quotientEquivAlg _ _ e hI)

/-- The original scalar triangle for the actual quotient base change. -/
theorem tensorQuotientSpanSingletonEquiv_comp_algebraMap (P : MvPolynomial σ R) :
    (tensorQuotientSpanSingletonEquiv (S := S) P).toRingEquiv.toRingHom.comp
      (algebraMap S (S ⊗[R] (MvPolynomial σ R ⧸ Ideal.span {P}))) =
        algebraMap S (MvPolynomial σ S ⧸ Ideal.span {map (algebraMap R S) P}) :=
  (tensorQuotientSpanSingletonEquiv (S := S) P).toAlgHom.comp_algebraMap

/-- Irreducibility of the same coefficient image makes the original tensor
quotient a domain. -/
theorem isDomain_tensor_quotient_of_irreducible_map
    {L : Type*} [Field L] [Algebra R L]
    (P : MvPolynomial σ R) (hP : Irreducible (map (algebraMap R L) P)) :
    IsDomain (L ⊗[R] (MvPolynomial σ R ⧸ Ideal.span {P})) := by
  let : (Ideal.span {map (algebraMap R L) P}).IsPrime :=
    (Ideal.span_singleton_prime hP.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hP)
  exact MulEquiv.isDomain (MvPolynomial σ L ⧸ Ideal.span {map (algebraMap R L) P})
    (tensorQuotientSpanSingletonEquiv (S := L) P).toMulEquiv

end MvPolynomial

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hypersurface

universe u v

variable {R : Type (max u v)} [CommRing R] {σ : Type v}

/-- The original hypersurface field base change is integral when its original
coefficient polynomial is irreducible. The tensor square retains both original
structural maps, not just an abstract isomorphism of underlying spaces. -/
theorem isIntegral_pullback_of_irreducible_map
    (P : MvPolynomial σ R) (L : Type (max u v)) [Field L] [Algebra R L]
    (hP : Irreducible (MvPolynomial.map (algebraMap R L) P)) :
    IsIntegral (pullback (Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {P}))
      (Spec.algebraMap R L) : Scheme.{max u v}) := by
  let B := MvPolynomial σ R ⧸ Ideal.span {P}
  let : IsDomain (L ⊗[R] B) := MvPolynomial.isDomain_tensor_quotient_of_irreducible_map P hP
  have H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R L B)).flip
  exact IsIntegral.of_isIso H.isoPullback.hom

/-- Fieldwise irreducibility on a fixed principal open gives geometric
integrality of the original hypersurface morphism restricted by that same
base change. -/
theorem geometricallyIntegral_principal_of_forall_irreducible_map
    (P : MvPolynomial σ R) (r : R)
    (h : ∀ (L : Type (max u v)) [Field L] (φ : R →+* L), φ r ≠ 0 →
      Irreducible (MvPolynomial.map φ P)) :
    GeometricallyIntegral (pullback.snd
      (Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {P}))
      (Spec.algebraMap R (Localization.Away r))) := by
  let f := Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {P})
  let b := Spec.algebraMap R (Localization.Away r)
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : Scheme.{max u v} → Prop) :=
    ⟨fun e hi => by
      let := hi
      exact IsIntegral.of_isIso e.hom⟩
  constructor
  refine (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral) (R := Localization.Away r) (f := pullback.snd f b)).mpr ?_
  intro L _ _
  let : Algebra R L := ((algebraMap (Localization.Away r) L).comp
    (algebraMap R (Localization.Away r))).toAlgebra
  let : IsScalarTower R (Localization.Away r) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hr : algebraMap R L r ≠ 0 := by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).map
      (algebraMap (Localization.Away r) L)
    exact hu.ne_zero
  have hi := isIntegral_pullback_of_irreducible_map P L (h L (algebraMap R L) hr)
  let s := Spec.algebraMap (Localization.Away r) L
  have hs : s ≫ b = Spec.algebraMap R L := by
    rw [← Spec.map_comp]
    congr 1
  have hj : IsIntegral (pullback f (s ≫ b) : Scheme.{max u v}) := by
    rw [hs]
    exact hi
  let := hj
  exact IsIntegral.of_isIso (pullbackLeftPullbackSndIso f b s).inv

/-- Generic absolute irreducibility spreads to geometrically integral fibres
of the same hypersurface over a nonzero principal open of the original domain. -/
theorem exists_ne_zero_geometricallyIntegral_principal
    [IsDomain R] [Finite σ] (K Ω : Type (max u v)) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    (P : MvPolynomial σ R) (hP : Irreducible (MvPolynomial.map (algebraMap R Ω) P)) :
    ∃ r : R, r ≠ 0 ∧ GeometricallyIntegral (pullback.snd
      (Spec.algebraMap R (MvPolynomial σ R ⧸ Ideal.span {P}))
      (Spec.algebraMap R (Localization.Away r))) := by
  obtain ⟨r, hr, h⟩ :=
    MvPolynomial.FactorizationAlgebra.exists_ne_zero_forall_irreducible_map R K Ω P hP
  exact ⟨r, hr, geometricallyIntegral_principal_of_forall_irreducible_map P r h⟩

end AlgebraicGeometry.Scheme.Hypersurface
