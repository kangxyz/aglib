/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Module length under surjective scalar localization

A surjective map of commutative scalar rings remains surjective after
localization at corresponding primes. For a module carrying both scalar
actions and their scalar tower, the actual localized tensor-product modules
have the same extended-natural length over the source and target local
rings. No finite-length assumption is imposed.

## Extraction basis

Transferred from `R5Lab.KTheory.Grayson.Cycle.LocalLength` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`12f3f8fbc4c284a725802bb602194f047b5963563237989bf5f46e58fdd1b8bf`.
This module contains the genuinely general `SurjectiveLocalization` section (source lines
22–68), preserving `localMap_surjective` and `length_localization_of_surjective`; all other
source interfaces remain outside this extraction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
universe u v w

section SurjectiveLocalization
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- A surjective coefficient map remains surjective at corresponding primes. -/
theorem _root_.Localization.localMap_surjective (h : Function.Surjective (algebraMap A B))
    (p : Ideal B) [p.IsPrime] :
    Function.Surjective (Localization.localRingHom (p.under A) p (algebraMap A B) rfl) := by
  have hm := Ideal.map_primeCompl_comap_of_surjective (algebraMap A B) h p
  let : IsLocalization ((p.under A).primeCompl.map (algebraMap A B))
      (Localization.AtPrime p) := by rw [hm]; infer_instance
  exact IsLocalization.map_surjective_of_surjective (p.under A).primeCompl
    (Localization.AtPrime (p.under A)) (Localization.AtPrime p) h

/-- The original module has the same local length over a surjective source ring
and its quotient, at corresponding primes. No finite-length assumption is used. -/
theorem length_localization_of_surjective (h : Function.Surjective (algebraMap A B))
    (p : Ideal B) [p.IsPrime] :
    Module.length (Localization.AtPrime (p.under A))
      (Localization.AtPrime (p.under A) ⊗[A] M) =
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[B] M) := by
  let := Localization.AtPrime.algebraOfLiesOver (p.under A) p
  let N := Localization.AtPrime p ⊗[B] M
  let : Module (Localization.AtPrime (p.under A)) N :=
    Module.compHom N (algebraMap (Localization.AtPrime (p.under A)) (Localization.AtPrime p))
  let : IsScalarTower A (Localization.AtPrime (p.under A)) N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change (algebraMap (Localization.AtPrime (p.under A)) (Localization.AtPrime p)
        (algebraMap A (Localization.AtPrime (p.under A)) a)) • n = a • n
      rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  let : IsScalarTower (Localization.AtPrime (p.under A)) (Localization.AtPrime p) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[B] N := _root_.TensorProduct.mk B (Localization.AtPrime p) M 1
  have hm := Ideal.map_primeCompl_comap_of_surjective (algebraMap A B) h p
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B (p.under A).primeCompl) f := by
    change IsLocalizedModule ((p.under A).primeCompl.map (algebraMap A B)) f
    rw [hm]
    infer_instance
  let : IsLocalizedModule (p.under A).primeCompl (f.restrictScalars A) :=
    IsLocalizedModule.restrictScalars _ f
  let e := (IsLocalizedModule.isBaseChange (p.under A).primeCompl
    (Localization.AtPrime (p.under A)) (f.restrictScalars A)).equiv
  rw [e.length_eq]
  apply Module.length_eq_of_surjective
  rw [Localization.AtPrime.algebraMap_eq]
  exact Localization.localMap_surjective h p
end SurjectiveLocalization

end Module
