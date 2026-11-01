/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GenericFreeness.Noetherian
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Generic fibrewise regularity of an original nonzero element

Generic flatness of the original quotient by an element makes its original
multiplication map injective after every field base change on one principal
open. The base algebra map is not assumed injective. Empty base changes are
allowed: multiplication on the zero algebra is injective as well.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open TensorProduct

namespace LinearMap

/-- After a flat base change makes the original cokernel flat, every further
scalar extension preserves the original left injection. All comparisons are
the native cancellation-of-base-change maps and their naturality law. -/
theorem lTensor_injective_of_flat_baseChange_cokernel
    {R S M N P A : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A] [Module S A]
    [IsScalarTower R S A] [Module.Flat R S] [Module.Flat S (S ⊗[R] P)]
    (g : M →ₗ[R] N) (q : N →ₗ[R] P) (hg : Function.Injective g)
    (hq : Function.Surjective q) (hex : Function.Exact g q) :
    Function.Injective (g.lTensor A) := by
  let gS := AlgebraTensorModule.lTensor S S g
  let qS := AlgebraTensorModule.lTensor S S q
  have hgS : Function.Injective gS := Module.Flat.lTensor_preserves_injective_linearMap g hg
  have hqS : Function.Surjective qS := LinearMap.lTensor_surjective S hq
  have hexS : Function.Exact gS qS := Module.Flat.lTensor_exact S hex
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat qS hqS gS hgS hexS A
  let eM := AlgebraTensorModule.cancelBaseChange R S S A M
  let eN := AlgebraTensorModule.cancelBaseChange R S S A N
  have hnat := AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := A) g
  have hcomm (x : A ⊗[R] M) :
      eN ((gS.lTensor A) (eM.symm x)) = (g.lTensor A) x := by
    change eN ((AlgebraTensorModule.lTensor S A gS) (eM.symm x)) =
      (AlgebraTensorModule.lTensor S A g) x
    have hh := congrArg (fun f => f (eM.symm x)) hnat
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      eM, eN, gS] using hh.symm
  intro x y hxy
  apply eM.symm.injective
  apply hinj
  apply eN.injective
  exact (hcomm x).trans (hxy.trans (hcomm y).symm)

end LinearMap

namespace Algebra

/-- A nonzero element of an original finite-type domain becomes regular in
every original field fibre over a nonzero principal open of the base domain.
There is no injectivity assumption on the original base algebra map. -/
theorem exists_ne_zero_forall_injective_mul_one_tmul
    (R B : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type*) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 →
        Function.Injective (fun x : L ⊗[R] B => ((1 : L) ⊗ₜ[R] b) * x) := by
  let I : Ideal B := Ideal.span {b}
  let Q := B ⧸ I
  let g : B →ₗ[R] B := LinearMap.mulLeft R b
  let q : B →ₗ[R] Q := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hg : Function.Injective g := fun x y h => mul_left_cancel₀ hb h
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hex : Function.Exact g q := by
    intro x
    change Ideal.Quotient.mk I x = 0 ↔ ∃ y, b * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      exact Ideal.mem_span_singleton.mpr ⟨y, rfl⟩
  obtain ⟨r, hr, hflat⟩ :=
    Module.Finite.exists_ne_zero_flat_localizedModule_away (A := R) (B := B) Q
  refine ⟨r, hr, ?_⟩
  intro L _ _ hrL
  let l : Localization.Away r →+* L :=
    IsLocalization.Away.lift (S := Localization.Away r) (g := algebraMap R L) r
      (isUnit_iff_ne_zero.mpr hrL)
  let : Algebra (Localization.Away r) L := l.toAlgebra
  let : IsScalarTower R (Localization.Away r) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.Away.lift_eq _ _ x).symm)
  let : Module.Flat (Localization.Away r) (LocalizedModule.Away r Q) := hflat
  let : Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] Q) :=
    Module.Flat.of_linearEquiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) Q).symm
  have hinj := LinearMap.lTensor_injective_of_flat_baseChange_cokernel
    (S := Localization.Away r) (A := L) g q hg hq hex
  have heq : g.lTensor L =
      LinearMap.mulLeft R ((1 : L) ⊗ₜ[R] b : L ⊗[R] B) := by
    ext a x
    change (g.lTensor L) (a ⊗ₜ[R] x) =
      ((1 : L) ⊗ₜ[R] b) * (a ⊗ₜ[R] x)
    simp only [g, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [heq] at hinj
  exact hinj

end Algebra
