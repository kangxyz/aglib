/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.FinitePresentation.FiniteStage

/-!
# Public fibrewise regularity supplier for arbitrary flat finitely presented algebras

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 3059–3060, 3079–3146, 3154–3170, 3227–3258.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

open Algebra.FlatApproximation

namespace Algebra



section BaseLocalTransport
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical ideal quotient structure used after localized-base transport. -/
local instance localizedBaseAtPrimeHasQuotient
    (q : Ideal S) [q.IsPrime]
    (Q : Ideal (Localization.AtPrime (q.under R) ⊗[R] S)) [Q.IsPrime] :
    HasQuotient (Localization.AtPrime Q) (Ideal (Localization.AtPrime Q)) :=
  @Ideal.instHasQuotient_1 (Localization.AtPrime Q) inferInstance

/-- Regularity and base-flatness at closed-fibre primes after localization of
the base transport to the actual local ring at the original prime. No
finiteness or flatness hypothesis on the original algebra is needed. -/
theorem regular_and_flat_atPrime_of_localizedBase
    (q : Ideal S) [q.IsPrime] (a : S)
    (hlocal : ∀ (Q : Ideal (Localization.AtPrime (q.under R) ⊗[R] S))
      [Q.IsPrime], Q.LiesOver
          (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))) →
      IsSMulRegular (Localization.AtPrime Q)
          (algebraMap (Localization.AtPrime (q.under R) ⊗[R] S)
            (Localization.AtPrime Q) ((1 : Localization.AtPrime (q.under R)) ⊗ₜ[R] a)) ∧
      Module.Flat (Localization.AtPrime (q.under R))
        (Localization.AtPrime Q ⧸ Ideal.span
          {algebraMap (Localization.AtPrime (q.under R) ⊗[R] S)
            (Localization.AtPrime Q) ((1 : Localization.AtPrime (q.under R)) ⊗ₜ[R] a)})) :
    IsSMulRegular (Localization.AtPrime q)
      (algebraMap S (Localization.AtPrime q) a) ∧
    Module.Flat R (Localization.AtPrime q ⧸ Ideal.span
      {algebraMap S (Localization.AtPrime q) a}) := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let B := Rp ⊗[R] S
  obtain ⟨Q, hQ, hQover, hQcomap⟩ := exists_prime_localizedBaseChange (R := R) q
  let := hQ
  let := hQover
  let T := Localization.AtPrime Q
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R S B := Algebra.TensorProduct.right_isScalarTower
  have : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) B :=
    IsLocalization.tensorRight Rp p.primeCompl
  have : IsScalarTower R S T := inferInstance
  have : IsLocalization.AtPrime T q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) T Q
    change IsLocalization.AtPrime T (Q.comap (algebraMap S B)) at h
    change Q.comap (algebraMap S B) = q at hQcomap
    simpa only [hQcomap] using h
  let e : T ≃ₐ[R] Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).restrictScalars R
  have hchosen : e (algebraMap B T ((1 : Rp) ⊗ₜ[R] a)) =
      algebraMap S (Localization.AtPrime q) a := by
    change (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q))
      (algebraMap B T ((1 : Rp) ⊗ₜ[R] a)) = _
    change (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q))
      (algebraMap B T (algebraMap S B a)) = _
    rw [← IsScalarTower.algebraMap_apply S B T]
    exact (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).commutes a
  obtain ⟨hreg, hflat⟩ := @hlocal Q hQ hQover
  let := hflat
  have : Module.Flat R Rp := IsLocalization.flat Rp p.primeCompl
  have : Module.Flat R (T ⧸ Ideal.span {algebraMap B T ((1 : Rp) ⊗ₜ[R] a)}) :=
    Module.Flat.trans R Rp _
  have hresult := regular_and_flat_of_algEquiv e
    (algebraMap B T ((1 : Rp) ⊗ₜ[R] a)) hreg
  rwa [hchosen] at hresult

end BaseLocalTransport
end Algebra

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The residue fibre of the algebra with localized base is the original
prime fibre, with the original equation carried by canonical pure tensors. -/
theorem residue_regular_localized_base (p : Ideal R) [p.IsPrime] (a : S)
    (ha : IsSMulRegular (p.Fiber S) ((1 : p.ResidueField) ⊗ₜ[R] a)) :
    IsSMulRegular ((Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p))
      ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] S))
      ((1 : Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p))
        ⊗ₜ[Localization.AtPrime p] ((1 : Localization.AtPrime p) ⊗ₜ[R] a)) :=
  (regular_tensor_model_iff (R := Localization.AtPrime p) (A := R)
    (K := p.ResidueField) (AlgEquiv.refl : Localization.AtPrime p ⊗[R] S ≃ₐ[Localization.AtPrime p]
      Localization.AtPrime p ⊗[R] S) a).mpr ha

end Algebra

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Fibrewise regularity of an equation in a flat finitely presented algebra
over an arbitrary base implies regularity and flatness of its actual principal
quotient. No Noetherian or reducedness assumption is made. -/
theorem regular_and_flat_of_fibre_regular
    [Algebra.FinitePresentation R S] [Module.Flat R S] (a : S)
    (ha : ∀ (p : Ideal R) [p.IsPrime],
      IsSMulRegular (p.Fiber S) ((1 : p.ResidueField) ⊗ₜ[R] a)) :
    IsSMulRegular S a ∧ Module.Flat R (S ⧸ Ideal.span {a}) := by
  have hq (q : Ideal S) [q.IsPrime] :
      IsSMulRegular (Localization.AtPrime q) (algebraMap S (Localization.AtPrime q) a) ∧
      Module.Flat R
        (Localization.AtPrime q ⧸ Ideal.span {algebraMap S (Localization.AtPrime q) a}) := by
    apply regular_and_flat_atPrime_of_localizedBase q a
    intro Q hQ hQover
    let := hQover
    exact regular_and_flat_at_prime_of_residue_regular
      ((1 : Localization.AtPrime (q.under R)) ⊗ₜ[R] a)
      (residue_regular_localized_base (q.under R) a (ha (q.under R))) Q
  constructor
  · exact regular_of_localized_maximal a (fun q _ ↦ (hq q).1)
  · apply flat_quotient_of_localized_maximal (Ideal.span {a})
    intro q hqmax
    have := (hq q).2
    let e : (Localization.AtPrime q ⧸ (Ideal.span {a}).map (algebraMap S (Localization.AtPrime q)))
        ≃ₐ[R] (Localization.AtPrime q ⧸ Ideal.span {algebraMap S (Localization.AtPrime q) a}) :=
      Ideal.quotientEquivAlgOfEq R (by simp [Ideal.map_span])
    exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Algebra
