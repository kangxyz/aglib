/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.StandardEtaleDomainEmbedding
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Hypersurface
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Geometric integrality of the original standard etale factor

The canonical polynomial-coordinate equivalence identifies the actual factor
quotient. Its original map into the standard etale algebra is injective and
stays injective after field extension. Hence an integral original scalar
extension forces the same coefficient polynomial to remain irreducible.
This is not yet a common-open spreading theorem for an arbitrary scheme.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace MvPolynomial

/-- The native coordinate equivalence on the actual factor quotient. -/
def adjoinRootFinSuccEquiv (K : Type*) [CommRing K] (n : ℕ)
    (p : Polynomial (MvPolynomial (Fin n) K)) :
    AdjoinRoot p ≃ₐ[K]
      MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {(finSuccEquiv K n).symm p} := by
  exact Ideal.quotientEquivAlg _ _ (finSuccEquiv K n).symm
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

end MvPolynomial

namespace StandardEtalePresentation

/-- If the original standard etale algebra remains a domain over a field
extension, its vanishing irreducible factor remains irreducible in the native
polynomial coordinates over that same field. -/
theorem irreducible_map_factor_of_isDomain_tensor
    {K L S : Type*} [Field K] [Field L] [CommRing S] [IsDomain S]
    [Algebra K L] [Algebra K S] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) K) S]
    [IsScalarTower K (MvPolynomial (Fin n) K) S]
    [IsDomain (L ⊗[K] S)]
    (P : StandardEtalePresentation (MvPolynomial (Fin n) K) S)
    (p q : Polynomial (MvPolynomial (Fin n) K))
    (hirr : Irreducible p) (hf : P.f = p * q) (hp : aeval P.x p = 0) :
    Irreducible (MvPolynomial.map (algebraMap K L)
      ((MvPolynomial.finSuccEquiv K n).symm p)) := by
  let F := (MvPolynomial.finSuccEquiv K n).symm p
  let B := MvPolynomial (Fin (n + 1)) K ⧸ Ideal.span {F}
  let e : AdjoinRoot p ≃ₐ[K] B := MvPolynomial.adjoinRootFinSuccEquiv K n p
  let j : B →ₐ[K] S :=
    ((AdjoinRoot.liftAlgHom p (Algebra.ofId _ S) P.x hp).restrictScalars K).comp e.symm.toAlgHom
  have hj : Function.Injective j :=
    (P.factor_lift_injective p q hirr hf hp).comp e.symm.injective
  let t : L ⊗[K] B →ₐ[K] L ⊗[K] S :=
    Algebra.TensorProduct.map (AlgHom.id K L) j
  have ht : Function.Injective t :=
    Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap hj
  let : IsDomain (L ⊗[K] B) := Function.Injective.isDomain t.toRingHom ht
  let : IsDomain (MvPolynomial (Fin (n + 1)) L ⧸
      Ideal.span {MvPolynomial.map (algebraMap K L) F}) :=
    MulEquiv.isDomain (L ⊗[K] B)
      (MvPolynomial.tensorQuotientSpanSingletonEquiv (S := L) F).symm.toMulEquiv
  have hF : F ≠ 0 := by
    intro h
    apply hirr.ne_zero
    exact (MvPolynomial.finSuccEquiv K n).symm.injective (h.trans (map_zero _).symm)
  have hFL : MvPolynomial.map (algebraMap K L) F ≠ 0 := by
    intro h
    apply hF
    exact MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
      (h.trans (map_zero _).symm)
  have hprime : (Ideal.span {MvPolynomial.map (algebraMap K L) F}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime
      (Ideal.span {MvPolynomial.map (algebraMap K L) F})).mp inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mpr
    ((Ideal.span_singleton_prime hFL).mp hprime)

end StandardEtalePresentation
