/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.FractionBase
public import Mathlib.RingTheory.Localization.BaseChange
public import Aglib.RingTheory.Excellent.RegularMap
public import Aglib.RingTheory.RegularLocalRing.Reduced
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reduced prime-base quotients of regular maps

Flatness embeds the tensor with a prime quotient into the tensor with its
residue field. The latter is regular under the original regular-map test.
The native quotient/tensor equivalence then gives reducedness of the actual
extended-prime quotient, without a Nagata or domain hypothesis on the base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace Algebra.IsRegularMap

/-- Every original prime-base quotient of a regular algebra map is reduced.
The quotient need not itself be a fibre; its injection into the residue-field
fibre is obtained by tensoring the original prime-quotient injection. -/
theorem isReduced_quotient_prime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsRegularMap R S) (p : Ideal R) [p.IsPrime] :
    IsReduced (S ⧸ p.map (algebraMap R S)) := by
  let : Module.Flat R S := h.1
  let : IsRegularRing (S ⊗[R] p.ResidueField) := h.2 p p.ResidueField
  let : IsReduced (S ⊗[R] p.ResidueField) := IsRegularRing.isReduced_of_regular _
  let φ : (R ⧸ p) →ₐ[R] p.ResidueField := IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField
  let ψ : (S ⊗[R] (R ⧸ p)) →ₐ[R] S ⊗[R] p.ResidueField :=
    Algebra.TensorProduct.map (AlgHom.id R S) φ
  have hψ : Function.Injective ψ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) φ.toLinearMap
      p.injective_algebraMap_quotient_residueField
  let : IsReduced (S ⊗[R] (R ⧸ p)) := isReduced_of_injective ψ hψ
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p
  exact isReduced_of_injective e e.injective

/-- Above the generic point of a domain, a regular map has regular actual
prime localizations. No zero-dimensionality of its generic fibre is asserted. -/
theorem isRegularLocalRing_atPrime_of_comap_eq_bot
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] (h : Algebra.IsRegularMap R S)
    (P : Ideal S) [P.IsPrime] (hP : P.comap (algebraMap R S) = ⊥) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  let T := FractionBaseLocalization.BaseLocalized R S
  let : IsRegularRing (S ⊗[R] FractionRing R) :=
    h.regular_finiteGenericFibre R S (FractionRing R) (FractionRing R)
  let e : (S ⊗[R] FractionRing R) ≃ₐ[S] T :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) _ _
  let : IsRegularRing T := IsRegularRing.of_ringEquiv e.toRingEquiv
  let : (FractionBaseLocalization.selectedPrime R S P).IsPrime :=
    FractionBaseLocalization.selectedPrime_isPrime R S P hP
  exact IsRegularLocalRing.of_ringEquiv
    (FractionBaseLocalization.localEquiv R S P hP).toRingEquiv

end Algebra.IsRegularMap
