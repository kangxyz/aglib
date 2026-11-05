/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.KernelNormalizationArrow
public import Aglib.RingTheory.Nagata.MinimalPrimeNormalizationCover

/-! # The complete normal-component family of an arbitrary Nagata arrow

Every actual minimal-prime quotient of the coefficient ring is retained.
Its original source arrow is first divided by its actual kernel and then
normalized. The resulting source and coefficient rings are normal Nagata
domains, the arrow between them is injective, and the original square
commutes. Both outside arrows are finite; the coefficient family covers
every original prime, including for a nonreduced coefficient ring.

The source family need not cover the original source spectrum. None of the
normalization squares is asserted Cartesian.
-/

@[expose] public noncomputable section

namespace RingHom.MinimalPrimeNormalization

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The original arrow to the literal coefficient component. -/
def componentArrow (p : minimalPrimes B) : A →+* B ⧸ p.val :=
  (Ideal.Quotient.mk p.val).comp f

/-- Normalizing the coefficient component does not alter the source kernel.
Thus the displayed source quotient is also the actual kernel quotient of the
original arrow into this normal coefficient domain. -/
theorem componentArrow_ker (p : minimalPrimes B) :
    RingHom.ker ((algebraMap B (Algebra.minimalPrimeNormalization B p)).comp f) =
      RingHom.ker (componentArrow f p) := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  have hinj : Function.Injective
      (algebraMap (B ⧸ p.val) (Algebra.minimalPrimeNormalization B p)) := by
    intro x y h
    apply IsFractionRing.injective (B ⧸ p.val) (FractionRing (B ⧸ p.val))
    have hh := congrArg (algebraMap (Algebra.minimalPrimeNormalization B p)
      (FractionRing (B ⧸ p.val))) h
    simpa only [← IsScalarTower.algebraMap_apply] using hh
  change RingHom.ker
    ((algebraMap (B ⧸ p.val) (Algebra.minimalPrimeNormalization B p)).comp
      (componentArrow f p)) = RingHom.ker (componentArrow f p)
  exact RingHom.ker_comp_of_injective _ hinj

/-- The normalization of the actual source kernel quotient for this component. -/
abbrev sourceComponent (p : minimalPrimes B) :=
  integralClosure (A ⧸ RingHom.ker (componentArrow f p))
    (FractionRing (A ⧸ RingHom.ker (componentArrow f p)))

/-- The original source-to-normal-component arrow. -/
def sourceMap (p : minimalPrimes B) : A →+* sourceComponent f p := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  exact KernelNormalization.sourceMap (componentArrow f p)

/-- The injective original normalization arrow on this component. -/
def componentMap (p : minimalPrimes B) :
    sourceComponent f p →+* Algebra.minimalPrimeNormalization B p := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  exact KernelNormalization.normalMap (componentArrow f p)

/-- Normalization retains the original arrow, including its kernel and the
original minimal-prime quotient on the coefficient side. -/
theorem componentMap_sourceMap (p : minimalPrimes B) :
    (componentMap f p).comp (sourceMap f p) =
      (algebraMap B (Algebra.minimalPrimeNormalization B p)).comp f := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  exact KernelNormalization.normalMap_sourceMap (componentArrow f p)

theorem componentMap_injective (p : minimalPrimes B) :
    Function.Injective (componentMap f p) := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  exact KernelNormalization.normalMap_injective (componentArrow f p)

/-- Finiteness of the displayed source arrow is supplied by the original
source Nagata hypothesis, not by a normalization-finite assumption. -/
theorem sourceMap_finite (hA : IsNagataRing.{u, 0} A) (p : minimalPrimes B) :
    (sourceMap f p).Finite := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  exact KernelNormalization.sourceMap_finite (componentArrow f p) hA

/-- Every source component is a normal Nagata domain, with its original
source rank bound. No injectivity of the original arrow is required. -/
theorem sourceComponent_properties (hA : IsNagataRing.{u, 0} A)
    (p : minimalPrimes B) :
    IsDomain (sourceComponent f p) ∧ IsIntegrallyClosed (sourceComponent f p) ∧
      IsNagataRing.{u, 0} (sourceComponent f p) ∧
      ringKrullDim (sourceComponent f p) ≤ ringKrullDim A := by
  let : IsDomain (B ⧸ p.val) := Algebra.minimalPrimeQuotient_isDomain B p
  let : IsDomain (A ⧸ RingHom.ker (componentArrow f p)) :=
    KernelNormalization.sourceDomain_isDomain (componentArrow f p)
  let : Algebra A (sourceComponent f p) := (sourceMap f p).toAlgebra
  let : Module.Finite A (sourceComponent f p) := sourceMap_finite f hA p
  exact ⟨inferInstance,
    (KernelNormalization.sourceNormal_properties (componentArrow f p) hA).2.1,
    IsNagataRing.of_finite hA,
    KernelNormalization.sourceNormal_ringKrullDim_le (componentArrow f p) hA⟩

/-- Every coefficient component is a normal Nagata domain, finite over the
original coefficient ring, with the unchanged induction-rank bound. -/
theorem coefficientComponent_properties (hB : IsNagataRing.{u, 0} B)
    (p : minimalPrimes B) :
    Module.Finite B (Algebra.minimalPrimeNormalization B p) ∧
      IsDomain (Algebra.minimalPrimeNormalization B p) ∧
      IsIntegrallyClosed (Algebra.minimalPrimeNormalization B p) ∧
      IsNagataRing.{u, 0} (Algebra.minimalPrimeNormalization B p) ∧
      ringKrullDim (Algebra.minimalPrimeNormalization B p) ≤ ringKrullDim B := by
  have h := Algebra.minimalPrimeNormalization_properties B hB p
  let : Module.Finite B (Algebra.minimalPrimeNormalization B p) := h.1
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, IsNagataRing.of_finite hB, h.2.2.2.2⟩

/-- Every prime of the original coefficient ring lifts to one of the actual
normal components. This is the component form of the proved whole-product
cover, not a covering assumption. -/
theorem exists_coefficientComponent_prime_over (hB : IsNagataRing.{u, 0} B)
    (q : PrimeSpectrum B) :
    ∃ (p : minimalPrimes B) (z : PrimeSpectrum (Algebra.minimalPrimeNormalization B p)),
      PrimeSpectrum.comap (algebraMap B (Algebra.minimalPrimeNormalization B p)) z = q := by
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  obtain ⟨Q, hQ⟩ := Algebra.minimalPrimeNormalizationProduct_comap_surjective B hB q
  obtain ⟨p, z, hz⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq Q
  refine ⟨p, z, ?_⟩
  exact (congrArg (PrimeSpectrum.comap
    (algebraMap B (Algebra.minimalPrimeNormalizationProduct B))) hz).trans hQ

end RingHom.MinimalPrimeNormalization
