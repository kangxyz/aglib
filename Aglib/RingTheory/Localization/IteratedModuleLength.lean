/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Iterated localization of module length

Localizing at a prime and then at a prime of that localization gives the same module length as
localization at the contracted prime. The canonical scalar maps also identify the actual
localization supports. No finite-length hypothesis is required.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.IteratedLocalizationLength` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`0bf5bd73c760e4024c7e066d80383546a19e7973b329afa9562fb58bfb642b1c`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
open _root_.TensorProduct
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Localizing M at Q and then at p gives the literal original localization
at P=p.under A, with equal lengths over the canonically isomorphic local rings. -/
theorem iterated_localized_length (Q : Ideal A) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[Localization.AtPrime Q] (Localization.AtPrime Q ⊗[A] M)) =
    Module.length (Localization.AtPrime (p.under A))
      (Localization.AtPrime (p.under A) ⊗[A] M) := by
  let B := Localization.AtPrime Q
  let C := Localization.AtPrime p
  let P := p.under A
  let D := Localization.AtPrime P
  let e : D ≃ₐ[A] C := IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl p
  let : Algebra D C := e.toRingHom.toAlgebra
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (e.commutes a).symm)
  let N := C ⊗[A] M
  let : Module D N := Module.compHom N e.toRingHom
  let : IsScalarTower A D N := IsScalarTower.of_algebraMap_smul fun a n => by
    change (e (algebraMap A D a)) • n = a • n
    rw [e.commutes, algebraMap_smul]
  let : IsScalarTower D C N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f : M →ₗ[A] N := _root_.TensorProduct.mk A C M 1
  let b := (IsLocalizedModule.isBaseChange P.primeCompl D f).equiv
  have hb : Module.length D (D ⊗[A] M) = Module.length D N := b.length_eq
  have hc : Module.length D N = Module.length C N :=
    Module.length_eq_of_surjective e.surjective
  have hcancel : Module.length C (C ⊗[B] (B ⊗[A] M)) = Module.length C N :=
    (AlgebraTensorModule.cancelBaseChange A B C C M :
      (C ⊗[B] (B ⊗[A] M)) ≃ₗ[C] N).length_eq
  exact hcancel.trans (hc.symm.trans hb.symm)

theorem mem_support_iff_localized_length_ne_zero (p : Ideal A) [p.IsPrime] :
    (⟨p, inferInstance⟩ : PrimeSpectrum A) ∈ Module.support A M ↔
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) ≠ 0 := by
  let e := IsLocalizedModule.iso p.primeCompl
    (_root_.TensorProduct.mk A (Localization.AtPrime p) M 1)
  rw [Module.mem_support_iff, ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
  exact ⟨fun h => by let := h; exact e.symm.nontrivial,
    fun h => by let := h; exact e.nontrivial⟩

theorem mem_support_localized_iff (Q : Ideal A) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    (⟨p, inferInstance⟩ : PrimeSpectrum (Localization.AtPrime Q)) ∈
        Module.support (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[A] M) ↔
      (⟨p.under A, inferInstance⟩ : PrimeSpectrum A) ∈ Module.support A M := by
  rw [mem_support_iff_localized_length_ne_zero, mem_support_iff_localized_length_ne_zero,
    iterated_localized_length Q p]

end Module
